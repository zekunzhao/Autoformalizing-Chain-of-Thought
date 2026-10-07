from os import listdir, walk
from os.path import isfile, join
import xml.etree.ElementTree as ET
import xml.dom.minidom
import re
import json

class Frameset(object):
    """docstring for Frameset"""
    def __init__(self, et, framename, version = "old"):
        super(Frameset, self).__init__()
        self.predicate_lemmas = {}
        predicates = et.findall('predicate')
        if version == "old":
            self.rolesetclass = RoleSet
        elif version == "new":
            self.rolesetclass = RoleSetNew
        else:
            self.rolesetclass = RoleSetProp

        self.no_rel = 0
        self.role_sets = []

        for pred in predicates:
            self.load_rolesets(pred, framename)

    def load_rolesets(self, predicate, framename):
        pred_lemma = predicate.get('lemma')
        self.predicate_lemmas[pred_lemma] = []

        # root = et.find('predicate')
        root = predicate
        for roleset in root.findall('roleset'):
            role_set_obj = self.rolesetclass(roleset, pred_lemma, framename)

            self.no_rel += role_set_obj.no_rel
            # have a more flattened roleset for a given frame file
            self.role_sets.append(role_set_obj)
            # have a more hierarchical rolset for each predicate
            self.predicate_lemmas[pred_lemma].append(role_set_obj)

class RoleSet(object):
    """docstring for RoleSet"""
    def __init__(self, roleset, pred_lemma=None):
        super(RoleSet, self).__init__()

        self.roleset_id = roleset.get('id')
        self.name = roleset.get('name')
        self.no_rel = 0

        # look for roles(set of roles), or role if singular
        try:
            roles = roleset.find('roles').findall('role')
        except:
            roles = roleset.findall('role')

        # look for example and the ref token
        self.sense_examples = self.parse_example(roleset)

        self.roles = []
        self.parse_roles(roles)

    def parse_roles(self, roles):
        for role_ in roles:
            self.roles.append(Role(role_))

    def parse_example(self, roleset):

        examples = roleset.findall('example')
        if len(examples) > 0:
            example_set = []
            for example in examples:

                try:
                    example_sent = example.find('text').text.lower()
                except:
                    if len(examples) > 1:
                        continue
                    else:
                        return None
                try:
                    tk_ref = example.find('rel').text.lower()
                except:

                    concept_lemma = self.roleset_id.split(".")[0].lower()
                    # sometimes the concept lemma contains dash and underscores
                    special_symbols = ["-", "_"]
                    for sym in special_symbols:
                        if sym in concept_lemma:
                            concept_lemma = concept_lemma.split(sym)[0]
                            break

                    concept_str_len = len(concept_lemma)
                    tks = example_sent.split(" ")
                    found = False

                    if concept_str_len < 8:
                        search_str = concept_lemma[:-2]
                    if concept_str_len >= 8:
                        search_str = concept_lemma[:5]

                    # lemma search
                    for tk in tks:
                        if search_str in tk:
                            found = True
                            tk_ref   = tk

                    # name search
                    if not found:
                        tk_ref = ""
                
                # get args 
                args = {arg_tag.n: arg_tag.text for arg_tag in example.findall('arg')}


                example_set.append({'snt': example_sent, 'tk_ref': tk_ref, 'args': args})

            return example_set
        else:
            return None

class RoleSetNew(object):
    """docstring for RoleSetNew"""
    def __init__(self, roleset, root_predicate, root_frame):
        super(RoleSetNew, self).__init__()
        self.ontonote_vn_map_pattern = re.compile(r'\(from [\w+ ]*\w+\.\d+\-*\w*[\w ]*\)')
        self.ontonote_vn_map_pattern2 = re.compile(r'\(from [\w+ ]*\w+\-*\w*\.\d+[\w ]*\)')
        self.vn_propb_pattern = re.compile(r'\w+\.\d+')
        self.vn_propb_pattern2 = re.compile(r'\w+\-\w\.\d+')

        roleset_id = roleset.get('id')

        self.roleset_id = roleset_id

        self.name = roleset.get('name')
        self.no_rel = 0
        # look for roles(set of roles), or role if singular
        try:
            roles = roleset.find('roles').findall('role')
        except:
            roles = roleset.findall('role')

        # look for example and the ref token
        self.vn_senses = []
        self.potential_ontonote_maps = self.parse_ontonote(roleset)
        self.sense_examples = self.parse_example(roleset, self.roleset_id)

        self.roles = []
        self.parse_roles(roles)
        self.root_predicate = root_predicate
        self.root_frame = root_frame

    def parse_ontonote(self, roleset):
        all_notes = roleset.findall('note')
        for note in all_notes:
            note_text = note.text.lower()
            vn_correspondence = self.ontonote_vn_map_pattern.findall(note_text)
            vn_correspondence2 = self.ontonote_vn_map_pattern2.findall(note_text)
            
            if len(vn_correspondence) > 0:
                for vn_str in vn_correspondence:

                    vn_role = self.vn_propb_pattern.findall(vn_str)[0]
                    if self.roleset_id == vn_role:
                        continue
                    else:
                        self.vn_senses.append(vn_role)
            if len(vn_correspondence2) > 0:
                for vn_str in vn_correspondence2:
                    vn_str = self.vn_propb_pattern2.findall(vn_str)[0]
                    vn_role = vn_str.split('-')[0]+vn_str[-3:]
                    if self.roleset_id == vn_role:
                        continue
                    else:
                        self.vn_senses.append(vn_role)



    def parse_roles(self, roles):
        for role_ in roles:
            self.roles.append(Role(role_))

    def parse_example(self, roleset, roleset_id=None):

        examples = roleset.findall('example')
        if len(examples) > 0:
            example_set = []
            for example in examples:

                example_sent = example.find('text').text.lower()

                tk_ref = example.find('rel').text.lower()

                # we have annotated all rel tag for examples in propbank

                if re.match(r'\w+_name', tk_ref):
                    # this meaning a special annotation appears, we need to extract meaning of this concept from other sources instead of the example text

                    source = tk_ref.split("_")[0]

                    if source == "example":
                        example_sent = example.attrib.get('name')
                        tk_ref = example_sent

                    elif source == "roleset":
                        example_sent = roleset.attrib.get('name')
                        tk_ref = example_sent
                    else:
                        print("exception: ", tk_ref)

                # get args 
            
                args = {arg_tag.attrib['n']: str(arg_tag.text) for arg_tag in example.findall('arg')}

                example_set.append({'snt': example_sent, 'tk_ref': tk_ref, 'args': args})

            return example_set
        else:
            return None

class RoleSetProp(object):
    """docstring for RoleSetNew"""
    def __init__(self, roleset, root_predicate, root_frame):
        super(RoleSetProp, self).__init__()
        self.ontonote_vn_map_pattern = re.compile(r'\(from [\w+ ]*\w+\.\d+\-*\w*[\w ]*\)')
        self.ontonote_vn_map_pattern2 = re.compile(r'\(from [\w+ ]*\w+\-*\w*\.\d+[\w ]*\)')
        self.vn_propb_pattern = re.compile(r'\w+\.\d+')
        self.vn_propb_pattern2 = re.compile(r'\w+\-\w\.\d+')

        roleset_id = roleset.get('id')

        self.roleset_id = roleset_id

        self.name = roleset.get('name')
        self.no_rel = 0
        # look for roles(set of roles), or role if singular
        try:
            roles = roleset.find('roles').findall('role')
        except:
            roles = roleset.findall('role')

        # look for example and the ref token
        self.vn_senses = []
        self.potential_ontonote_maps = self.parse_ontonote(roleset)
        self.sense_examples = self.parse_example(roleset, self.roleset_id)

        self.roles = []
        self.parse_roles(roles)
        self.root_predicate = root_predicate
        self.root_frame = root_frame

    def parse_ontonote(self, roleset):
        all_notes = roleset.findall('note')
        for note in all_notes:
            try:
                note_text = note.text.lower()
            except:
                continue
            vn_correspondence = self.ontonote_vn_map_pattern.findall(note_text)
            vn_correspondence2 = self.ontonote_vn_map_pattern2.findall(note_text)
            
            if len(vn_correspondence) > 0:
                for vn_str in vn_correspondence:

                    vn_role = self.vn_propb_pattern.findall(vn_str)[0]
                    if self.roleset_id == vn_role:
                        continue
                    else:
                        self.vn_senses.append(vn_role)
            if len(vn_correspondence2) > 0:
                for vn_str in vn_correspondence2:
                    vn_str = self.vn_propb_pattern2.findall(vn_str)[0]
                    vn_role = vn_str.split('-')[0]+vn_str[-3:]
                    if self.roleset_id == vn_role:
                        continue
                    else:
                        self.vn_senses.append(vn_role)



    def parse_roles(self, roles):
        for role_ in roles:
            self.roles.append(Role(role_))

    def parse_example(self, roleset, roleset_id=None):

        examples = roleset.findall('example')
        if len(examples) > 0:
            example_set = []
            for example in examples:
                if example.find('text').text:
                    example_sent = example.find('text').text.lower()
                elif example.find('amr'):
                    # this is an AMR case.
                    # print(ET.tostring(example, encoding='unicode'))
                    # print('-'*80)
                    example_sent = example.find('amr').text
                elif example.find('umr'):
                    example_sent = example.find('umr').text
                else:
                    # print(ET.tostring(example, encoding='unicode'))
                    # print('-'*80)
                    continue

                if example.find('propbank'):
                    propb = example.find('propbank')
                    if propb.find('rel'):
                        tk_ref = propb.find('rel').text.lower()
                    else:
                        tk_ref = ''
                    
                    # we have annotated all rel tag for examples in propbank

                    if re.match(r'\w+_name', tk_ref):
                        print('tk_ref match _name pattern: ', tk_ref)
             
                    arg_tags = propb.findall('arg')
                    args = []

                    for arg_tag in arg_tags:
                        arg_fn = arg_tag.attrib['type']
                        if arg_fn.startswith('R-') or arg_fn.startswith('C-'):
                            continue
                        if '-' in arg_fn:
                            fn_pieces = arg_fn[3:].split('-')
                            try:
                                n = fn_pieces[0]
                                f = fn_pieces[1]
                            except:
                                print('arg_fn: ', arg_fn)
                                print(roleset.get('id'))
                                exit()
                        else:
                            n = arg_fn[3:]
                            f = ''

                        args.append({'arg_text': str(arg_tag.text), 'f': f, 'n': n})

                    example_set.append({'name': example.attrib['name'], 'snt': example_sent, 'tk_ref': tk_ref, 'args': args})
                else:
                    example_set.append({'name': example.attrib['name'], 'snt': example_sent, 'tk_ref': '', 'args': []})
            return example_set
        else:
            return []

class Role(object):
    """docstring for Role"""
    def __init__(self, role_):
        super(Role, self).__init__()
        self.description = role_.get('descr')

        self.function = role_.get('f')
        self.index = role_.get('n')
        try:
            index = int(self.index)
        except:
            index_holder = self.index
            self.index = self.function
            self.function = index_holder


    def __str__(self):
        return self.function+"-"+self.index

class PropbankFrames(object):
    """docstring for PropbankFrames"""
    def __init__(self, propbank_frames_path, version="new"):
        super(PropbankFrames, self).__init__()
        self.propbank_frames_path = propbank_frames_path
        self.frame_dict = {}
        self.version = version

        self.no_rel = 0


    @staticmethod
    def read_frame_file(root, file_name, version = "old"):
        with open(join(root, file_name), 'r') as file_handle:
            tree = ET.parse(file_handle)

            # for pred in tree.findall('predicate'):
            framename = file_name.split('.')[0]
            frameset = Frameset(tree, framename=framename, version=version)
        return frameset, framename

    def load(self):
        for root, dirs, files in walk(self.propbank_frames_path):
            assert len(dirs) == 0
            for file in files:
                if not file.endswith('xml'):
                    continue

                # every frame file contains several predicates
                frameset, framename = self.__class__.read_frame_file(root, file, self.version)

                
                self.frame_dict[framename] = frameset
                self.no_rel += frameset.no_rel

    def get_roleset(self, roleset_name):
        try:
            roles = self.rolesets[roleset_name]
            return roles
        except:
            return []

    def roleset_dict(self):
        self.rolesets = {}
        self.rolesets_index = {}
        counter = 0
        for framename, frameset in self.frame_dict.items():
            for lemma, rolesets in frameset.predicate_lemmas.items():
                for roleset in rolesets:

                    if roleset.roleset_id not in self.rolesets:
                        self.rolesets[roleset.roleset_id] = roleset
                        self.rolesets_index[roleset.roleset_id] = counter
                        counter += 1

    def save_rolesets_as_json(self, json_file_path):
        rolesets = {'propbank_rolesets': []}
        for roleset_id, roleset in self.rolesets.items():
            rolesets['propbank_rolesets'].append({
                "roleset_id": roleset.roleset_id,
                "roleset_name": roleset.name,
                "roles":  [{
                    "descr": role.description,
                    "f": role.function,
                    "n": role.index,
                    "vnroles": roleset.vn_senses,
                    } for role in roleset.roles
                ],
                "examples": [{
                    "example_name": example['name'],
                    "example_text": example['snt'],
                    "args": example['args'], 
                    "rel": {'rel_text': example['tk_ref']}
                } for example in roleset.sense_examples
                ],
            })
        with open(json_file_path, 'w') as f:
            json.dump(rolesets, f, indent=2)

def main():
    raise SystemExit('This module is a library; use translate.py.')


if __name__ == '__main__':
    main()
