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
  let src := s!"inductive RoleTag where
  | {joined}
  deriving DecidableEq, Repr"
  match Parser.runParserCategory (← getEnv) `command src with
  | Except.ok stx => elabCommand stx
  | Except.error err => throwError "parser error in macro expansion: {err}"
| _ => throwUnsupportedSyntax

#genRoleTag PAG, PPT
-- Reusable role assignment structure
structure RoleAssignment (E T : Type) where
  role : RoleTag
  event : E
  value : T

-- Generic predicate for checking role assignment
def bindsTo {E T : Type} (r : RoleAssignment E T) (e : E) (t : T) (tag : RoleTag) : Prop :=
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
        `(def $(mkIdent lcName) {E T : Type} (e : E) (x : T)
            : RoleAssignment E T :=
              { role  := $(mkIdent roleCtor)
              , event := e
              , value := x })

      /- predicate: OP1 e x : Prop ------------------------------------- -/
      let pred ←
        `(def $(mkIdent tagId) {E T : Type} (e : E) (x : T) : Prop :=
            bindsTo ($(mkIdent lcName) e x) e x $(mkIdent roleCtor))

      elabCommand ctor
      elabCommand pred
| _ => throwUnsupportedSyntax

#genRoleHelpers [PAG, PPT]   -- run it once



-- natural language description: Someone baked a cake.
axiom ax_bake_01_s0b:
 ∃ s0b : Event,
 ∃ s0p : Entity,
 ∃ s0c : Entity,
 s0b.name = "bake-01" ∧
 PAG s0b s0p ∧
 PPT s0b s0c ∧
 s0p.name = "person" ∧
 s0c.name = "cake"

-- [Optional knowledge insertion point: extra axioms may be added here if needed]


-- natural language description: A cake was baked.
theorem thm_bake_01_s1b :
 ∃ s1b : Event,
 ∃ s1c : Entity,
 s1b.name = "bake-01" ∧
 PPT s1b s1c ∧
 s1c.name = "cake" := by
  sorry