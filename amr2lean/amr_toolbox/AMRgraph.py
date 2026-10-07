import penman
from penman.models.amr import model
from penman.transform import reify_edges, canonicalize_roles
from penman.codec import PENMANCodec
from penman.models.noop import NoOpModel
from penman.transform import indicate_branches
from penman.graph import Triple, Instance, Edge, Attribute, Graph

import json
import copy
import re
import os

dir_path = os.path.dirname(os.path.realpath(__file__))
amr_role_file_path = os.path.join(dir_path, "AMR-roles.json")
with open(amr_role_file_path, "r") as f:
    official_amr_roles = json.load(f)

relation_dict = {}
for role_type, roles in official_amr_roles.items():
    for role in roles:
        if role not in model.roles:
            model.roles[role] = {'type': role_type}

            # print("new role added from official amr roles dictionary")
            # print(role, ": ", "{'type: '", role_type)
for role in model.roles:
    relation_dict[role] = len(relation_dict)

attribute_rels = [':pl', ':mode']
class AMRNode(object):
    """docstring for AMRNode"""
    def __init__(self, var_name, text, type_="concept", coordinate=()):
        super(AMRNode, self).__init__()
        self.var_name = var_name
        self.text = text
        self.type = type_
        self.children = {}
        self.parents = {}
        self.level = 0
        self.index = 0
        self.unique_text = None
        self.clone_origin = None
        self.clone_copies = 0
        self.coordinate = coordinate
        self.meta = {}

    def __str__(self):
        return self.var_name+" \\ "+self.text

    def add_parent(self, parent_node, relation_type):
        self.parents[parent_node] = relation_type

    def add_children(self, child_node, relation_type):
        self.children[child_node] = relation_type

    def has_children(self):
        if len(self.children) != 0:
            return True
        else:
            return False


class AMRTree(object):
    """docstring for AMRTree"""
    def __init__(self, amr_str, propbank_rolesets=None):
        super(AMRTree, self).__init__()
        self.amr_str = amr_str
        self.codec = PENMANCodec(model=NoOpModel())
        # amr_penman_graph = self.codec.decode(amr_str)
        amr_penman_graph = penman.decode(self.amr_str, NoOpModel())

        self.amr_penman_graph = amr_penman_graph
        self.edge_dict = {}
        self.node_dict = {}
        self.attribute_dict = {}
        self.top = None
        self.roots = []
        self.visited_node = []
        self.levels = {}
        self.propbank_rolesets = propbank_rolesets

        # self.construct_graph()
        self.construct_tree()
        # if len(self.roots) == 0:
        #     self.roots = [self.node_dict[self.amr_penman_graph.top]]
        # print(self.node_dict)
        # print(self.edge_dict)
        # self.construct_tree()
        # resurface the node
        self.node_resurface()

        self.predicate_pattern = re.compile(r'[a-z\-]+-\d+')

    def edge_dict_update(self, node1, node2, relation):
        if (node1.var_name, node2.var_name) in self.edge_dict:

            self.edge_dict[(node1.var_name, node2.var_name)].append(relation)
        else:
            self.edge_dict[(node1.var_name, node2.var_name)] = [relation]
    def node_relation_update(self, parent_node, child_node, relation):
        parent_node.add_children(child_node, relation)
        child_node.add_parent(parent_node, relation)

    def normalize_text(self, text):
        if self.predicate_pattern.match(text):
            if text not in self.propbank_frames.rolesets:
                text = re.sub(r'-\d+', "", text)
        return text

    def construct_graph(self):
        for inst in self.amr_penman_graph.instances():
            concept_name = self.normalize_text(str(inst.target))
            self.node_dict[inst.source] = AMRNode(str(inst.source), concept_name, "concept")

        attr_idx = 0
        self.top = self.node_dict[self.amr_penman_graph.top]
        for attribute in self.amr_penman_graph.attributes():
            attr_node_var = "attr-"+str(attr_idx)
            self.node_dict[attr_node_var] = AMRNode(attr_node_var
                , str(attribute.target), "attribute")

            self.attribute_dict[(attribute.source, attribute.role, attribute.target)] = attr_node_var
            attr_idx += 1

        branch_indicated_graph = indicate_branches(self.amr_penman_graph, model)

        relation_structure = {}

        for triplet in branch_indicated_graph.triples:
            if triplet[1] == ":TOP":
                relation_structure[(triplet[0], triplet[2])] = "p"
                relation_structure[(triplet[2], triplet[0])] = "c"


        for triplet in self.amr_penman_graph.triples:

            if triplet[1] == ":instance" or triplet[1] == ":wiki":
                continue

            else:

                source_node = self.node_dict[triplet[0]]
                try:
                    # regular participant role
                    target_node = self.node_dict[triplet[2]]
                except:
                    # attribute relations
                    target_node_var = self.attribute_dict[triplet]
                    target_node = self.node_dict[target_node_var]

            if (source_node.var_name, target_node.var_name) in relation_structure:
                structure = relation_structure[(source_node.var_name, target_node.var_name)]
            else:
                structure = "p"

            if structure == "p":
                source_node, target_node = self.check_reentrancy(source_node, target_node, structure, self.top)
                self.edge_dict_update(source_node, target_node, triplet[1])
                self.node_relation_update(source_node, target_node, triplet[1])
            else:
                source_node, target_node = self.check_reentrancy(source_node, target_node, structure, self.top)
                self.edge_dict_update(target_node, source_node, triplet[1]+"-of")
                self.node_relation_update(target_node, source_node, triplet[1]+"-of")

    def named_entity_filter(self, text):
        text_ = str(text)
        if text_.startswith('"') and text_.endswith('"'):
            text_ = text_[1:-1]
        return text_

    def construct_tree(self):
        for inst in self.amr_penman_graph.instances():
            text_ = self.named_entity_filter(str(inst.target))
            self.node_dict[inst.source] = AMRNode(str(inst.source), text_, "concept")

        attr_idx = 0
        self.top = self.node_dict[self.amr_penman_graph.top]
        for attribute in self.amr_penman_graph.attributes():
            attr_node_var = "attr-"+str(attr_idx)
            text_ = self.named_entity_filter(str(attribute.target))
            self.node_dict[attr_node_var] = AMRNode(attr_node_var
                , text_, "attribute")

            self.attribute_dict[(attribute.source, attribute.role, text_)] = attr_node_var
            attr_idx += 1

        amr_tree = self.codec.parse(self.amr_str)
        # nodes_str = list(amr_tree.nodes())

        for node in amr_tree.nodes():
            node_var_name = node[0]
            node_children = node[1][1:]

            node_obj = self.node_dict[node_var_name]
            for child in node_children:

                relation = child[0]
                child_node = child[1]

                if relation == ":wiki":
                    continue
                if isinstance(child_node, str):
                    # terminal node
                    # print("str: ", node_var_name, ": ", "-", child[0], "->", child[1])
                    child_node = self.named_entity_filter(child_node)
                    if child_node in self.node_dict:
                        # a terminal concept node & a reentrancy node
                        origin_node = self.node_dict[child_node]
                        origin_node.clone_copies += 1
                        dup_node_var = origin_node.var_name+"-copy-"+str(origin_node.clone_copies)
                        dup_node = AMRNode(dup_node_var, origin_node.text, "concept")
                        self.node_dict[dup_node_var] = dup_node
                        child_node_obj = dup_node
                    else:
                        # a terminal attribute
                        attr_node_var = self.attribute_dict[(node_var_name, relation, child_node)]
                        child_node_obj = self.node_dict[attr_node_var]
                    self.edge_dict_update(node_obj, child_node_obj, relation)
                    self.node_relation_update(node_obj, child_node_obj, relation)
                else:
                    # print("node: ", node_var_name, ": ", "-", child[0], "->", child[1][0])
                    # non-terminal node
                    child_node_obj = self.node_dict[child_node[0]]
                    self.edge_dict_update(node_obj, child_node_obj, relation)
                    self.node_relation_update(node_obj, child_node_obj, relation)


    def BFS_traverse(self, s, print_opt=False):

        # Mark all the vertices as not visited
        # print("enter BFS")
        visited = {var_name: False for var_name, node in self.node_dict.items()}
        levels = {var_name: None for var_name, node in self.node_dict.items()}
        # Create a queue for BFS
        queue = []

        # Mark the source node as
        # visited and enqueue it
        queue.append(s)
        visited[s.var_name] = True
        levels[s.var_name] = 0
        bfs_linearization_ls = []

        while queue:

            # Dequeue a vertex from
            # queue and print it
            s = queue.pop(0)

            # print(s.text)
            # print(levels[s.var_name])
            # print("-"*60)

            # Get all adjacent vertices of the
            # dequeued vertex s. If a adjacent
            # has not been visited, then mark it
            # visited and enqueue it
            if not s.var_name.startswith("attr-") and len(s.children) != 0:
                bfs_linearization_ls.append(s)
            
            for child_node, relation in s.children.items():
                # print(child_node.text, relation)
                if "-copy-" in child_node.var_name:
                    pruned_var_name = child_node.var_name.split("-copy-")[0]
                else:
                    pruned_var_name = child_node.var_name

                if visited[child_node.var_name] == False:
                    new_child_node = child_node
                    if pruned_var_name == child_node.var_name:
                        queue.append(child_node)
                    else:
                        new_child_node = self.node_dict[pruned_var_name]
                    visited[child_node.var_name] = True

                    if print_opt:
                        print("child_node: ", child_node.var_name, " ", child_node.text)

                    levels[child_node.var_name] = levels[s.var_name] + 1
                    bfs_linearization_ls += [relation, new_child_node]
            if len(s.children) != 0:

                bfs_linearization_ls.append("|")

        self.levels = levels
        if len(bfs_linearization_ls) == 0:
            # handle single node case
            bfs_linearization_ls += [s, "|"]
        return self.levels, bfs_linearization_ls

    def BFS_walk(self, s, with_var=False):
        levels, bfs_li_ls = self.BFS_traverse(s)
        bfs_li_ls = self.token_reorganize(bfs_li_ls, with_var=with_var)
        return bfs_li_ls

    def node_resurface(self):
        # this function is to uniquely assign new surface form for AMR nodes
        resurfaced_node_dict = {}
        # surface_set = {"tk1": ["tk1_var1"], "tk2": ["tk2_var1", "tk2_var2"]}
        surface_set = {}

        for node_var, node in self.node_dict.items():

            if node.text not in surface_set:
                surface_set[node.text] = [node_var]
                resurfaced_node_dict[node_var] = node.text
            else:
                node.unique_text = node.text+"-diff-"+str(len(surface_set[node.text]))
                resurfaced_node_dict[node_var] = node.unique_text
                
                surface_set[node.text].append(node_var)
                
        self.resurfaced_node_dict = resurfaced_node_dict

    def token_reorganize(self, linearization_ls, with_var=False):
        reorganized_ls = []
        visited_node_dict = {}

        
        for idx in range(len(linearization_ls)):
            element = linearization_ls[idx]
            if isinstance(element, str):
                # a relation or pipe token
                if element.startswith(":op"):
                    element = ":op"
                elif element.startswith(":snt"):
                    element = ":snt"

                reorganized_ls.append(element)
            else:
                # a node
                if element.type == "attribute":
                    reorganized_ls += ['"'+element.text+'"']
                    visited_node_dict[element] = element.var_name
                    continue

                new_node = True
                if element in visited_node_dict:
                    new_node = False

                if with_var:
                    if new_node:
                        var_index = "vv"+str(len(visited_node_dict))
                        reorganized_ls += [element.text, var_index]
                        visited_node_dict[element] = var_index

                    else:
                        reorganized_ls.append(visited_node_dict[element])

                else:
                    surface_form = element.text
                    if element.unique_text != None:
                        surface_form = element.unique_text


                    tokens = []
                    if "-diff-" in surface_form:
                        tokens = surface_form.split("-diff-")
                    else:
                        tokens = [surface_form]

                    reorganized_ls += tokens

        return reorganized_ls
            

    def DFS_trav(self, v, dfs_linearization_ls, with_open_parenthesis):

        for child_node, relation in v.children.items():
            # relations

            if relation.endswith("-of"):
                dfs_linearization_ls += [relation[:-3], "-of"]
            else:
                dfs_linearization_ls.append(relation)

            # if include open parenthesis
            if with_open_parenthesis:
                dfs_linearization_ls.append('(')

            if child_node.type == "attribute":
                dfs_linearization_ls.append(child_node)
                # all attribute nodes should be terminal nodes
            elif "-copy-" in child_node.var_name:
                pruned_chlid_var = child_node.var_name.split("-copy-")[0]
                dfs_linearization_ls.append(self.node_dict[pruned_chlid_var])
            else:
                dfs_linearization_ls.append(child_node)
                self.DFS_trav(child_node, dfs_linearization_ls, with_open_parenthesis)
            dfs_linearization_ls.append(")")

    def DFS_walk(self, s, with_var, with_open_parenthesis=False):

        dfs_linearization_ls = ['(', s]

        self.amr_surface_distinction = {}

        # we distinguish same concept but different variables/symbols

        self.DFS_trav(s, dfs_linearization_ls, with_open_parenthesis)
        dfs_linearization_ls.append(")")

        dfs_linearization_ls = self.token_reorganize(dfs_linearization_ls, with_var=with_var)
        return dfs_linearization_ls

    def DFS_plain(self, dfs_linearization_ls):
        dfs_plain_ls = ["("]
        i = 0
        while i < len(dfs_linearization_ls):
            
            if dfs_linearization_ls[i].startswith(":"):
                if dfs_linearization_ls[i+1] == "-of":
                    dfs_plain_ls += [dfs_linearization_ls[i], dfs_linearization_ls[i+1], "("]
                    i += 2
                else:
                    dfs_plain_ls += [dfs_linearization_ls[i], "("]
                    i += 1
            else:
                dfs_plain_ls.append(dfs_linearization_ls[i])
                i += 1
        return dfs_plain_ls


name_node_pttn = re.compile(r'^name(?:~\d+(?:,\d+)*)?$')
aligned_node_pttn = re.compile(r'^([-A-Za-z0-9._\'"]+)(?:~(\d+(?:,\d+)*))?$')
class PenmanAMRTree(object):
    """docstring for AMRTree"""
    def __init__(self, amr_str, propbank_rolesets=None, remove_alignmark=False):
        super(PenmanAMRTree, self).__init__()
        self.amr_str = amr_str
        self.codec = PENMANCodec(model=NoOpModel())
        # amr_penman_graph = self.codec.decode(amr_str)
        self.amr_tree = penman.parse(self.amr_str)

        self.edge_dict = {}
        self.node_dict = {}
      
        self.top = None
        self.max_lvl = 1

        self.levels = {}
        self.propbank_rolesets = propbank_rolesets

        # self.construct_graph()
        self.traverse_steps = self.construct_tree(remove_alignmark)
        self.top = self.node_dict[self.amr_tree.node[0]]
        # if len(self.roots) == 0:
        #     self.roots = [self.node_dict[self.amr_penman_graph.top]]
        # print(self.node_dict)
        # print(self.edge_dict)
        # self.construct_tree()
        # resurface the node
        # self.node_resurface()

        self.predicate_pattern = re.compile(r'[a-z\-]+-\d+')
        
    def add_sent_mark(self, sentmark):
        # go through the node_dict and create a mapping between old and new node names
        node_name_map = {}
        for node_var, node in self.node_dict.items():
            node_prefix = sentmark

            new_node_var = ''
            if node_var.startswith('attr-'):
                node_suffix = node_var[5:]
                new_node_var = 'attr-' + sentmark + 'a'+node_suffix
            else:
                new_node_var = sentmark + node_var
            node_name_map[node_var] = new_node_var

        # start updating the two major recording keeping storage node_dict and edge_dict
        # 1. node_dict clean up
        new_node_dict = {}
        for node_var, node in self.node_dict.items():
            new_node_var = node_name_map[node_var]
            # 1.1 update node internal attribute `var_name`
            node.var_name = new_node_var
            new_node_dict[new_node_var] = node
            
        new_edge_dict = {}
        for (source_var, target_var), rel in self.edge_dict.items():
            new_src_var = node_name_map[source_var]
            new_tgt_var = node_name_map[target_var]

            new_edge_dict[(new_src_var, new_tgt_var)] = rel

        # 2. replace the old record w/ the new record
        self.node_dict = new_node_dict
        self.edge_dict = new_edge_dict


    def edge_dict_update(self, node1, node2, relation):
        if (node1.var_name, node2.var_name) in self.edge_dict:

            self.edge_dict[(node1.var_name, node2.var_name)].append(relation)
        else:
            self.edge_dict[(node1.var_name, node2.var_name)] = [relation]
    def node_relation_update(self, parent_node, child_node, relation):
        parent_node.add_children(child_node, relation)
        child_node.add_parent(parent_node, relation)

    def normalize_text(self, text):
        if self.predicate_pattern.match(text):
            if text not in self.propbank_frames.rolesets:
                text = re.sub(r'-\d+', "", text)
        return text

    def construct_tree(self, remove_alignmark):
        pre_var = [self.amr_tree.node[0]]
        pre_rel = None
        pre_node = []
        pre_indexs = ()
        attr_idx = 0
        traverse_steps = []


        for step in self.amr_tree.walk():
               # if step[1][0] == '/':
            # print("step: ", step)
            if len(step[0]) > self.max_lvl:
                self.max_lvl = len(step[0])
            if len(step[0]) < len(pre_indexs):
                # print('condition1: len(step[0]) < len(pre_indexs), pre_indexs:', pre_indexs )
                for i in range(len(pre_indexs) - len(step[0])):
                    pre_var.pop()
                    pre_node.pop()

            if step[0][-1] == 0:
                # definition step
                # print('condition2: step[0][-1] == 0')
                concept_name = step[1][1]
                
              
                if remove_alignmark:
                    m = aligned_node_pttn.fullmatch(concept_name)
                    if m:
                        concept_name = m.group(1)


                if pre_var[-1] in self.node_dict:
                    # print('condition2.1: if pre_var[-1] in self.node_dict, pre_var: ', pre_var, ' | self.node_dict.keys(): ', self.node_dict.keys())
                    self.node_dict[pre_var[-1]].text = concept_name
                    if self.node_dict[pre_var[-1]].level > len(step[0]):
                        self.node_dict[pre_var[-1]].level = len(step[0])
                else:
                    # print('condition2.2: pre_var[-1] not in self.node_dict, pre_var: ', pre_var, ' | self.node_dict.keys(): ', self.node_dict.keys())
                    node_obj = AMRNode(pre_var[-1], concept_name, "concept", step[0])
                    node_obj.level = len(step[0])
                    self.node_dict[pre_var[-1]] = node_obj
                
                if pre_rel != None and len(pre_node) > 0:
                    # print('condition2.3: pre_rel != None and len(pre_node) > 0, pre_rel: ', pre_rel, ' | pre_node: ', pre_node)
                    # ready to deposit the cached relation
                    traverse_steps.append([pre_node[-1].var_name, node_obj.var_name, pre_rel])
                    self.edge_dict_update(pre_node[-1], node_obj, pre_rel)
                    self.node_relation_update(pre_node[-1], node_obj, pre_rel)
                    pre_rel = None
                pre_node.append(node_obj)

            else:
                # print('condition3: step[0][-1] != 0')
                # relation step
                relation = step[1][0]
                if relation == ':wiki':
                    continue
                # peak ahead 1 step
                next_node = step[1][1]


                if type(next_node) == tuple:
                    # sub tree continues
                    # peak ahead for node variable name and cache them
                    # print("condition3.1 record the var: ", next_node[0])
                    pre_var.append(next_node[0])
                    pre_rel = relation

                else:
                    # print('condition3.2 re-entrancy or attribute')
                    # re-entrancy string type and it must has alreay been introduced
                    # or attribute leaf
                    child_node_var = next_node
                    true_child_node_text = ""
                    m = aligned_node_pttn.fullmatch(child_node_var)
                    if m:
                        true_child_node_text = m.group(1)
                    else:
                        true_child_node_text = next_node

                    if remove_alignmark:
                        
                        child_node_var = true_child_node_text


                    if (re.match(r'\d+', child_node_var) 
                        or child_node_var.startswith('"') 
                        or relation in attribute_rels 
                        or true_child_node_text.strip() in ['-', '+', 'some']):
                        # print('condition3.2.1: attribute: ', child_node_var)

                        child_node_obj = AMRNode("attr-"+str(attr_idx), child_node_var.strip(), 'attribute', (*step[0], 0))
                        child_node_obj.level = len(step[0])
                        self.node_dict["attr-"+str(attr_idx)] = child_node_obj
                        attr_idx += 1
                    else:
                        # print('condition3.2.2: re-entrancy: child_node_var: ', child_node_var)

                        # could be a messed up instance that has def later
                        if child_node_var in self.node_dict:
                            # print('condition3.2.2.1: child_node_var in self.node_dict: ')
                            child_node_obj = self.node_dict[child_node_var]
                        else: 
                            # print('condition3.2.2.2: child_node_var not in self.node_dict')

                            child_node_obj = AMRNode("attr-"+str(attr_idx),child_node_var.strip(), 'attribute', len(step[0]))
                                # child_node_obj.level = len(step[0])
                            self.node_dict['attr-'+str(attr_idx)] = child_node_obj
                            attr_idx += 1
                    traverse_steps.append([pre_node[-1], child_node_obj.var_name, relation])
                    self.edge_dict_update(pre_node[-1], child_node_obj, relation)
                    self.node_relation_update(pre_node[-1], child_node_obj, relation)
            pre_indexs = step[0]
        return traverse_steps

    def BFS_traverse(self, s, print_opt=False):

        # Mark all the vertices as not visited
        # print("enter BFS")
        visited = {var_name: False for var_name, node in self.node_dict.items()}
        levels = {var_name: None for var_name, node in self.node_dict.items()}
        # Create a queue for BFS
        queue = []

        # Mark the source node as
        # visited and enqueue it
        queue.append(s)
        visited[s.var_name] = True
        levels[s.var_name] = 0
        bfs_linearization_ls = []

        while queue:

            # Dequeue a vertex from
            # queue and print it
            s = queue.pop(0)

            # print(s.text)
            # print(levels[s.var_name])
            # print("-"*60)

            # Get all adjacent vertices of the
            # dequeued vertex s. If a adjacent
            # has not been visited, then mark it
            # visited and enqueue it
            if not s.var_name.startswith("attr-") and len(s.children) != 0:
                bfs_linearization_ls.append(s)
            
            for child_node, relation in s.children.items():
                # print(child_node.text, relation)
                if "-copy-" in child_node.var_name:
                    pruned_var_name = child_node.var_name.split("-copy-")[0]
                else:
                    pruned_var_name = child_node.var_name

                if visited[child_node.var_name] == False:
                    new_child_node = child_node
                    if pruned_var_name == child_node.var_name:
                        queue.append(child_node)
                    else:
                        new_child_node = self.node_dict[pruned_var_name]
                    visited[child_node.var_name] = True

                    if print_opt:
                        print("child_node: ", child_node.var_name, " ", child_node.text)

                    levels[child_node.var_name] = levels[s.var_name] + 1
                    bfs_linearization_ls += [relation, new_child_node]
            if len(s.children) != 0:

                bfs_linearization_ls.append("|")

        self.levels = levels
        if len(bfs_linearization_ls) == 0:
            # handle single node case
            bfs_linearization_ls += [s, "|"]
        return self.levels, bfs_linearization_ls

    def BFS_walk(self, s, with_var=False):
        levels, bfs_li_ls = self.BFS_traverse(s)
        bfs_li_ls = self.token_reorganize(bfs_li_ls, with_var=with_var)
        return bfs_li_ls

    def node_resurface(self):
        # this function is to uniquely assign new surface form for AMR nodes
        resurfaced_node_dict = {}
        # surface_set = {"tk1": ["tk1_var1"], "tk2": ["tk2_var1", "tk2_var2"]}
        surface_set = {}

        for node_var, node in self.node_dict.items():

            if node.text not in surface_set:
                surface_set[node.text] = [node_var]
                resurfaced_node_dict[node_var] = node.text
            else:
                node.unique_text = node.text+"-diff-"+str(len(surface_set[node.text]))
                resurfaced_node_dict[node_var] = node.unique_text
                
                surface_set[node.text].append(node_var)
                
        self.resurfaced_node_dict = resurfaced_node_dict

    def token_reorganize(self, linearization_ls, with_var=False):
        reorganized_ls = []
        visited_node_dict = {}

        
        for idx in range(len(linearization_ls)):
            element = linearization_ls[idx]
            if isinstance(element, str):
                # a relation or pipe token
                if element.startswith(":op"):
                    element = ":op"
                elif element.startswith(":snt"):
                    element = ":snt"

                reorganized_ls.append(element)
            else:
                # a node
                if element.type == "attribute":
                    reorganized_ls += ['"'+element.text+'"']
                    visited_node_dict[element] = element.var_name
                    continue

                new_node = True
                if element in visited_node_dict:
                    new_node = False

                if with_var:
                    if new_node:
                        var_index = "vv"+str(len(visited_node_dict))
                        reorganized_ls += [element.text, var_index]
                        visited_node_dict[element] = var_index

                    else:
                        reorganized_ls.append(visited_node_dict[element])

                else:
                    surface_form = element.text
                    if element.unique_text != None:
                        surface_form = element.unique_text


                    tokens = []
                    if "-diff-" in surface_form:
                        tokens = surface_form.split("-diff-")
                    else:
                        tokens = [surface_form]

                    reorganized_ls += tokens

        return reorganized_ls
            

    def DFS_trav(self, v, dfs_linearization_ls, with_open_parenthesis):

        for child_node, relation in v.children.items():
            # relations

            if relation.endswith("-of"):
                dfs_linearization_ls += [relation[:-3], "-of"]
            else:
                dfs_linearization_ls.append(relation)

            # if include open parenthesis
            if with_open_parenthesis:
                dfs_linearization_ls.append('(')

            if child_node.type == "attribute":
                dfs_linearization_ls.append(child_node)
                # all attribute nodes should be terminal nodes
            elif "-copy-" in child_node.var_name:
                pruned_chlid_var = child_node.var_name.split("-copy-")[0]
                dfs_linearization_ls.append(self.node_dict[pruned_chlid_var])
            else:
                dfs_linearization_ls.append(child_node)
                self.DFS_trav(child_node, dfs_linearization_ls, with_open_parenthesis)
            dfs_linearization_ls.append(")")

    def DFS_walk(self, s, with_var, with_open_parenthesis=False):

        dfs_linearization_ls = ['(', s]

        self.amr_surface_distinction = {}

        # we distinguish same concept but different variables/symbols

        self.DFS_trav(s, dfs_linearization_ls, with_open_parenthesis)
        dfs_linearization_ls.append(")")

        dfs_linearization_ls = self.token_reorganize(dfs_linearization_ls, with_var=with_var)
        return dfs_linearization_ls

    def DFS_plain(self, dfs_linearization_ls):
        dfs_plain_ls = ["("]
        i = 0
        while i < len(dfs_linearization_ls):
            
            if dfs_linearization_ls[i].startswith(":"):
                if dfs_linearization_ls[i+1] == "-of":
                    dfs_plain_ls += [dfs_linearization_ls[i], dfs_linearization_ls[i+1], "("]
                    i += 2
                else:
                    dfs_plain_ls += [dfs_linearization_ls[i], "("]
                    i += 1
            else:
                dfs_plain_ls.append(dfs_linearization_ls[i])
                i += 1
        return dfs_plain_ls



    def penman_print(self):
        # use triplet to construct penman graph
        amr_triples = []
        top_node = None
        for node_var, node in self.node_dict.items():

            if not node_var.startswith('attr-'):
                penman_node = Instance(source=node_var, role=':instance', target=node.text)
                amr_triples.append(penman_node)
            
        for source_target_pair, relations in self.edge_dict.items():
            
            source_node_var, target_node_var = source_target_pair
            for relation in relations:
                if target_node_var.startswith('attr-'):
                    # attribute
                    target_node_text = self.node_dict[target_node_var].text
                    amr_triples.append(Attribute(source=source_node_var, role=relation, target=target_node_text))
                else:
                    # regular node
                    amr_triples.append(Edge(source=source_node_var, role=relation, target=target_node_var))

        amr_graph = Graph(amr_triples)
        # print('amr_triples:', amr_triples)
        penman_str = penman.encode(amr_graph, top=self.top.var_name, indent=2)
        return penman_str

strip_quotes = lambda s: s[1:-1] if s.startswith('"') and s.endswith('"') else s

def name_reconstructor(op_nodes):
    text_align_marks = [op_node.text.split('~') for op_node in op_nodes]
    combined_text = [strip_quotes(tam[0]) for tam in text_align_marks]
    all_align_marks = []
    for tam in text_align_marks:
        if len(tam) > 1:
            all_align_marks += tam[1].split(',')
    all_distinct_AM = list(set(all_align_marks))
    new_name_str = '"'+"_".join(combined_text)+'"'
    if len(all_distinct_AM) > 0:
        new_name_str += '~'+",".join(all_distinct_AM)

    return new_name_str


def name_collapser(amr_obj):
    attr_node_count = len([node for node_var, node in amr_obj.node_dict.items() if node.type == "attribute"])
    name_nodes = []
    for var, node in amr_obj.node_dict.items():
        if name_node_pttn.match(node.text):
            name_nodes.append(node)

    for node in name_nodes:
        # we need to collapse
        # create a new node.
        attr_node_var = "attr-"+str(attr_node_count)
        name_str = name_reconstructor([node for node, rel in node.children.items()])
        new_attr_node = AMRNode(attr_node_var, name_str, "attribute")
        attr_node_count += 1
        amr_obj.node_dict[attr_node_var] = new_attr_node
        for pnode in node.parents:
            amr_obj.node_relation_update(pnode, new_attr_node, ":name")
            amr_obj.edge_dict_update(pnode, new_attr_node, ":name")
        # no further child nodes other than the name strings 
        # remove the name subgraph all together
        for child_node in node.children:
            del amr_obj.node_dict[child_node.var_name]
            del amr_obj.edge_dict[(node.var_name, child_node.var_name)]

        node.children = []

        # remove the name node now after cleaning it
        for parent in node.parents:
            del amr_obj.edge_dict[(parent.var_name, node.var_name)]
            del parent.children[node]
        del amr_obj.node_dict[node.var_name]

    return amr_obj

