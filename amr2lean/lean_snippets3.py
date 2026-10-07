"""
Lean 4 syntax is hard‑coded.
"""

STRUCTURE_TMPL  = """structure {lemma}_{sense} {type_params} where
{fields}"""

NON_CORE_PRED_TMPL = """structure {lemma} (E T : Type) where
  event: E
  value: T"""

NON_CORE_ROLE_PRED_TMPL = """def {noncore_name}ROLE {{D E A : Type}} (d : D) (e : E) (a : A) : Prop := 
  d.event = e ∧ d.value = a"""

# INSTANCE_TMPL   = "def {var} : {type} := {value}"
INSTANCE_TMPL   = 'def {var} : {type} :=  ⟨"{text}"⟩'

MODIFIER_INST_TMPL = 'def {name} := ⟨"{modifier_name}" {modifyee}⟩'

AXIOM_TMPL      = "axiom {label} : {event_pred} ({type}) {var}"


GENERIC_STRUCT_TMPL = """structure {name} {type_params} where
{fields}"""

SPECIAL_ENTITY_TMPL = """structure {name} where
{fields}"""


COMPOUND_TMPL = 'let {name} := Compound{ent_or_event} ConnectorType.{connector_type} [{e_list}]'

ROLE_ASSIGN_STRU_TMPL = "{indent}let {role_id} := {role} {pred} {arg}"

ROLE_ASSIGN_PRED_TMPL = "{indent}{role} {role_id} {pred} {arg}"

ROLE_ASSIGN_PRED_TMPL_S = "{indent}{role} {pred} {arg}"
CONST_LET_DECLARE_TMPL = '{indent}let {concept} : {type} := ⟨"{concept_name}"⟩'

ROLE_PREDS = '''\
import Lean

open Lean Elab Command Meta

structure Entity where
  name : String

structure Event where
  name : String

structure Modifier where 
  name : String

structure Connector where
  name : String

syntax (name := genRoleTag) "#genRoleTag" ident,+ : command

@[command_elab genRoleTag]
def elabGenRoleTag : CommandElab
| `( #genRoleTag $idents:ident,* ) => do
  let ctorList := (idents.getElems.map (·.getId.toString)).toList
  let joined := " | ".intercalate ctorList
  let src := s!"inductive RoleTag where\n  | {{joined}}\n  deriving DecidableEq, Repr"
  match Parser.runParserCategory (← getEnv) `command src with
  | Except.ok stx => elabCommand stx
  | Except.error err => throwError "parser error in macro expansion: {{err}}"
| _ => throwUnsupportedSyntax

#genRoleTag {roles}
-- Reusable role assignment structure
structure RoleAssignment (E T : Type) where
  role : RoleTag
  event : E
  value : T

-- Generic predicate for checking role assignment
def bindsTo {{E T : Type}} (r : RoleAssignment E T) (e : E) (t : T) (tag : RoleTag) : Prop :=
  r.event = e ∧ r.value = t ∧ r.role = tag

-- === Macro ===

/-- improved helper macro ----------------------------------------------- -/
syntax (name := genRoleHelpers) "#genRoleHelpers" "[" ident,+ "]" : command

@[command_elab genRoleHelpers]
def elabRoleHelpers : CommandElab
| `(command| #genRoleHelpers [ $tags:ident,* ]) => do
    for tg in tags.getElems do
      /- names ---------------------------------------------------------- -/
      let tagId    := tg.getId                 -- e.g. `OP1`
      let lcName   := Name.mkSimple <| (tagId.toString.toLower)  -- `op1`
      let roleCtor := Name.append `RoleTag tagId                 -- `RoleTag.OP1`

      /- constructor: op1 e x : RoleAssignment ------------------------- -/
      let ctor ←
        `(def $(mkIdent lcName) {{E T : Type}} (e : E) (x : T)
            : RoleAssignment E T :=
              {{ role  := $(mkIdent roleCtor)
              , event := e
              , value := x }})

      /- predicate: OP1 e x : Prop ------------------------------------- -/
      let pred ←
        `(def $(mkIdent tagId) {{E T : Type}} (e : E) (x : T) : Prop :=
            bindsTo ($(mkIdent lcName) e x) e x $(mkIdent roleCtor))

      elabCommand ctor
      elabCommand pred
| _ => throwUnsupportedSyntax

#genRoleHelpers [{roles}]   -- run it once

'''
