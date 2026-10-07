from typing import List
import os, re
from pydantic import BaseModel


AMR_Role_cheat_sheet = "Reading the roles prelude\n"\
  "1) Roles"\
  "   #genRoleTag PAG, POSSESSIVE, PART, PPT"\
  "   ⇨"\
  "   inductive RoleTag | PAG | POSSESSIVE | PART | PPT"\
  "   (plus DecidableEq, Repr)\n"\
  "2) Uniform triple"\
  "   structure RoleAssignment (E T : Type) :="\
  "     (role : RoleTag) (event : E) (value : T)\n"\
  ") Primitive predicate"\
  "   def bindsTo {E T : Type} (r : RoleAssignment E T) (e : E) (x : T) (tag : RoleTag) : Prop :="\
  "     r.event = e ∧ r.value = x ∧ r.role = tag\n"\
  "4) Helpers per role (from #genRoleHelpers [R₁, R₂, …])"\
  "   For each role R:"\
  "     • r : {E T} → E → T → RoleAssignment E T      -- lowercase constructor"\
  "     • R : {E T} → E → T → Prop                    -- uppercase proposition"\
  "       R e x  ≡  bindsTo (r e x) e x RoleTag.R\n"\
  "5) Reading idiom"\
  "   • r e x   = the data triple ⟨role=R, event=e, value=x⟩"\
  "   • R e x   = the fact/Prop asserting that triple\n"\
  "6) Prover tips"\
  "   • To use R e x:  dsimp [R, r, bindsTo] at h; rcases h with ⟨rfl, rfl, rfl⟩"\
  "   • To prove R e x: dsimp [R, r, bindsTo]; exact ⟨rfl, rfl, rfl⟩"

AMR_Frame_cheat_sheet = "Reading the roles prelude\n"\
    "•  Frames = records. Each predicate instance is a structure with optional core roles: arg0..arg4 : Option _. Unknown → none.\n"\
    "•  Facts = quantified FOL statements. Sentences are axiom ax_sN_* : ∃ …, frame = { … } ∧ atoms….\n"\
    "•  Non-core = atoms. Modifiers/attributes/links are binary predicates (… → … → Prop) over basics (Entity, String, monetary_quantity_*, Prep, …).\n"\
    "•  Names & indices. price_01_s6p: PropBank sense + sentence index; trailing letter is the root predicate var name for uniqueness.\n"\
    "•  Reading order. (1) record equality = which roles are filled; (2) attached atoms = values/ops/modifiers.\n"\
    "•  Derivations. theorem lem/thm_sN_* assert derived equalities etc.; optional `knowledge insertion` lines above can add arithmetic/co-ref rules."

CCG_cheat_sheet = "Core types & predicates\n"\
    " • ι: individuals; ε: events\n"\
    " • Verbs/events: buy, pay, discount : ε → Prop\n"\
    " • Nouns/adjectives/numbers: price, item, original, customer, n_22 : ι → Prop\n"\
    " • Roles: Subj : ε → ι, Acc : ε → ι\n"\
    " • Links/preps: at, on, LEFTB : ε → ι → Prop\n"\
    "Axioms (facts)\n"\
    "Each axiom encodes a sentence as FOL: existentially introduce individuals/events and assert predicate atoms plus any equalities (co-ref) and links.\n"\
    "Theorems (goals)\n"\
    "Each theorem states a claim—also in FOL over the same vocabulary—to be proved from the axioms (optionally with small background rules like arithmetic or co-ref)."
Auto_cheat_sheet = "\n"

class State(BaseModel):
    body:str = ""                       # the description of AMR-lean
    PITs:List[str] = []                 # all PITs, including axiom, lemma and theorem
    axioms_provided:List[int] = []      # the list of int describing index of provided axioms in PITs
    unused:List[int] = []               # the list of int describing index of unused reasoning steps in PITs
    theorems:List[int] = []             # the list of int describing index of provided theorems in PITs
    axioms_added:List[str] = []         # axioms added by LLM
    proof_tactics:List[str] = []        # proof tactics for each lemma and theorem
    axioms_filtered_feedback:str = ""   # feedback for LLM when conclusion-related axioms were filtered out
    lean_messge:str = ""            # the message of lean system
    round:int = 0                   # number of rounds
    max_round:int = 1       # max number of querying LLM
    file_path:str = ""              # path to the lean file
    out_path: str = ""
    preflight_ok: bool = False
    style: str = "Auto"

def read_file(path, out_path, style, rounds):
    # read file and create initial state

    # check validility of file path
    match = re.search(r"[^\\/]+$", path)
    if match is not None:
        file_name = match.group(0)
    else:
        raise FileNotFoundError
    
    # create log file
    # with open(path.replace(file_name, "") + f"./log_" + STYLE + f"_" + file_name[:-4] + f"txt", "w", encoding = "utf-8") as file:
    #     pass

    # read lean file from the given path
    with open(path, "r", encoding = "utf-8") as file:
        cot = "".join(file.readlines())
    
    # split the file into body and PITs, each natural language description with its code is a chunk
    match = re.search(r"-- (natural language description|NL)", cot)
    if match is not None:
        body = cot[:match.start(0)].strip("\n") + "\n"
        rest = cot[match.start(0):].strip("\n")
        if "-- natural language description" in rest:
            PITs = ["-- natural language description" + i for i in rest.split("-- natural language description") if i != ""]
        else:
            PITs = ["-- NL" + i for i in rest.split("-- NL") if i != ""]
    else:
        raise Exception
    
    # get the type of each code chunk
    axioms = []
    unused = []
    theorems = []
    for i in range(len(PITs)):
        if "FAILED!" in PITs[i]:
            unused.append(i)
        elif "\naxiom" in PITs[i]:
            axioms.append(i)
        elif "\nlemma" in PITs[i]:
            unused.append(i)
        elif "\ntheorem" in PITs[i]:
            theorems.append(i)

    return State(
        body = body,
        PITs = PITs,
        axioms_provided = axioms,
        unused = unused,
        theorems = theorems,
        file_path = path,
        out_path = out_path,
        style = style,
        max_round = rounds
    )
