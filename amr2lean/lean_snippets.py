"""
Lean 4 syntax is hard‑coded.
"""
INDUCTIVE_TMPL = """inductive {name} where\n| mk : {name}"""

NON_CORE_PRED_TMPL = """structure {lemma} (E T : Type) where
  event: E
  value: T"""

NON_CORE_ROLE_PRED_TMPL = """def {noncore_name}ROLE {{D E A : Type}} (d : D) (e : E) (a : A) : Prop := 
  d.event = e ∧ d.value = a"""

INSTANCE_TMPL   = "def {var} : {type} := {value}"

ABBREV_TMPL = "abbrev {abbrev_name} : {type_sig}"

AXIOM_TMPL      = "axiom {label} : {event_pred} ({type}) {var}"

# NON_CORE_PRED_TMPL = "def {name} {{E F : Type}} (e : E) (f : F) : Prop := True"

EVENT_FUN_DEFS = """\
def Veridical    (X : Type) (x : X) : Prop := True
def NonVeridical (X : Type) (x : X) : Prop := True
def Approx       (X : Type) (x : X) : Prop := True
def E4C (X : Type) (x : X) : Prop := True  -- exists entity for connector proposition
"""


# GENERIC_STRUCT_TMPL = """structure {name} {type_params} where
# {fields}"""

GENERIC_STRUCT_TMPL = """structure {name} where
{fields}"""

SPECIAL_ENTITY_TMPL = """structure {name} where
{fields}"""

COMPOUND_EVENT_TMPL = """structure compound_event_{N} {type_params} where
{fields}"""

COMPOUND_TMPL = """structure compound_{N} {type_params} where
{fields}"""

COMPOUND_ENT_TMPL = """structure compound_ent_{N} {type_params} where
{fields}"""
MODIFIER_INST_TMPL = 'def {name} {type_sig} := ⟨{instants}⟩'

NON_CORE_ROLE_AXIOM_TMPL = 'axiom {role_name} : {modifiee_type} → {modifier_type} → Prop '
NON_CORE_ROLE_PRED_TMPL = '{indent}{role_name} {modifiee_var} {modifier_var}'

CONST_LET_DECLARE_ENTITY_TMPL = '{indent}let {concept} : {type} := ⟨"{concept_name}"⟩'
CONST_LET_DECLARE_STRUCT_TMPL = '{indent}let {concept} : {type} := {{ {arg_str} }}'
QUANT_DECLARE_STRUCT_TMPL = '{indent}{pred_var} = {{ {arg_str} }}'