import os
import re
"""
 a AMR loading class for LDC release amr file format 
 this class assum the AMR data are in text file with the following format
 # ::id 001
 # ::snt this is the sentence
 (b / be 
    :ARG0 (t / this)
    :ARG1 (s / sentence)
 )

 # ::id 002
 # ::snt this is another sentence
 (b / be 
    :ARG0 (t / this)
    :ARG1 (s / sentence 
        :mod (a / another)
    )
 )
"""
def replace_parentheses_with_spaces_except_within_quotes(input_string):
    result = ""
    is_within_quotes = False

    for char in input_string:
        if char == '"':
            is_within_quotes = not is_within_quotes

        if char == '(' and not is_within_quotes:
            result += '( '
        elif char == ')' and not is_within_quotes:
            result += ' )'
        else:
            result += char

    return result

class AMRLoader(object):
    """docstring for AMRLoader."""

    def __init__(self, amr_file_dir):
        super(AMRLoader, self).__init__()
        self.amr_file_dir = amr_file_dir

        self.states_reverse_transit_rules = {
            "start": ["meta", "start"],
            "meta": ["meta", "amr"],
            "amr": ["amr", "start"],
            }
        self.state_from_parent_rules = {
            "meta": ["start", "meta"],
            "start": ["start", "amr"],
            "amr": ["amr", "meta"],
        }
        self.wiki_pattern = r'\s:wiki\s"[^"]*"'


    def read_all_amr(self, group_by_file=True, keep_indentation=False):
        if group_by_file:
            all_data = {}
            sorted_lst = sorted(os.listdir(self.amr_file_dir))
            for file in sorted_lst:
                file_path = os.path.join(self.amr_file_dir, file)

                if os.path.isfile(file_path):
                    try:
                        meta_datas_amrs = self.read_amrs(file_path, keep_indentation)
                        all_data[file] = meta_datas_amrs
                    except:
                        # not valid amr data file
                        print("problematic amr found in: ", file_path)
            return all_data
        else:
            all_data = []
            sorted_lst = sorted(os.listdir(self.amr_file_dir))
            for file in sorted_lst:
                file_path = os.path.join(self.amr_file_dir, file)

                if os.path.isfile(file_path):
                    try:
                        meta_datas_amrs = self.read_amrs(file_path, keep_indentation)
                        all_data += meta_datas_amrs
                    except:
                        # not valid amr data file
                        print("problematic amr found in: ", file_path)
            return all_data            

    def identify_line_state(self, line, prev_state):
        if line.startswith("# ::") and prev_state in self.state_from_parent_rules["meta"]:
            return "meta"
        elif line.strip() == "" and prev_state in self.state_from_parent_rules["start"]:
            return "start"
        elif line.strip() != "" and prev_state in self.state_from_parent_rules["amr"]:
            return "amr"
        else:
            return "error"



    def amr_cleaner(self, text):
        text = re.sub(self.wiki_pattern, '', text)
        text = replace_parentheses_with_spaces_except_within_quotes(text)
        return text

    def read_amrs(self, file_path, keep_indentation=False):
        state = "start"

        meta_amrs = []
        filename = file_path.split("/")[-1]
        count = 0
        with open(file_path, "r") as f:
            # mm = mmap.mmap(f.fileno(), 0)
            meta = []
            amr = []

            for line_idx, line in enumerate(f.readlines()):
                cur_state = self.identify_line_state(line, state)
                
                if cur_state == "meta":
                    meta.append(line.strip())
                elif cur_state == "amr":
                    if keep_indentation:
                        amr.append(line)
                    else:
                        amr.append(line.strip())
                elif cur_state == "error":
                    cur_state = "start"
                    meta = []
                    amr = []
                else:
                    if len(meta) > 0 and len(amr) > 0:
                        id_str = None
                        snt_str = None
                        other_meta = [f"# ::seg-file {filename}"]
                        for m in meta:
                            if m.startswith("# ::id"):
                                id_str_raw = m[len("# ::id "):]
                                id_str = id_str_raw.split()[0].strip()
                            elif m.startswith("# ::snt"):
                                snt_str = m[len("# ::snt "):]
                            else:
                                other_meta.append(m)
                        if id_str == None:
                            id_str = filename + "-" +str(count)
                        cleaner_amr = self.amr_cleaner(" ".join(amr))
                        # cleaner_amr = re.sub(self.wiki_pattern, '', cleaner_amr)
                        meta_amrs.append({"meta": other_meta, "amr": cleaner_amr, "snt": snt_str, "id": id_str})
                        count += 1
                    meta = []
                    amr = []
                state = cur_state
            if len(meta) > 0 and len(amr) > 0:
                id_str = None
                snt_str = None
                other_meta = [f"# ::seg-file {filename}"]
                for m in meta:
                    if m.startswith("# ::id"):
                        id_str = m[len("# ::id "):]
                    elif m.startswith("# ::snt"):
                        snt_str = m[len("# ::snt "):]
                    else:
                        other_meta.append(m)
                if id_str == None:
                    id_str = filename + "-" +str(count)
                cleaner_amr = self.amr_cleaner(" ".join(amr))
                # cleaner_amr = re.sub(self.wiki_pattern, '', cleaner_amr)
                meta_amrs.append({"meta": other_meta, "amr": cleaner_amr, "snt": snt_str, "id": id_str})
        return meta_amrs

    def save_amrs(self, data, saving_path):
        with open(saving_path, "w") as f:
            for meta_amr in data:
                f.write("# ::id "+meta_amr["id"]+"\n")
                for meta_info in meta_amr["meta"]:
                    f.write(meta_info+"\n")
                f.write("# ::snt "+meta_amr["snt"]+"\n")
                f.write(meta_amr["amr"])
                f.write("\n\n")
