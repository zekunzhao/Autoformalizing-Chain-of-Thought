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

#genRoleTag PPT, PAG
-- Reusable role assignment structure
structure RoleAssignment (E T : Type) where
  role : RoleTag
  event : E
  value : T

-- Generic predicate for checking role assignment
def bindsTo {E T : Type} (r : RoleAssignment E T) (e : E) (t : T) (tag : RoleTag) : Prop :=
  r.event = e ∧ r.value = t ∧ r.role = tag

-- === Macro ===

syntax (name := defRoleHelpers) "#genRoleHelpers" "[" ident,+ "]" : command

@[command_elab defRoleHelpers]
def elabRoleHelpers : CommandElab
| `(command| #genRoleHelpers [ $ids:ident,* ]) => do
  for id in ids.getElems do
    let roleName : Name := id.getId
    let ctorName := Name.mkSimple roleName.toString.toLower
    let binderName := Name.mkSimple roleName.toString.toUpper
    let ctorIdent := mkIdent ctorName
    let binderIdent := mkIdent binderName

    -- Use explicit qualified name for RoleTag constructor
    let roleCtor := mkIdent (``RoleTag ++ roleName)

    let ctor ← `(def $ctorIdent {E T : Type} (e : E) (x : T) : RoleAssignment E T :=
      { role := $roleCtor, event := e, value := x })

    let binder ← `(def $binderIdent {E T : Type} (r : RoleAssignment E T) (e : E) (x : T) : Prop :=
      bindsTo r e x $roleCtor)

    elabCommand ctor
    elabCommand binder
| _ => throwUnsupportedSyntax

#genRoleHelpers [PPT, PAG]


-- natural language description: Someone baked a cake.
axiom ax_bake_01_s0b:
 ∃ s0b : Event,
 ∃ s0p : Entity,
 ∃ s0c : Entity,
 let s0b_s0p := pag s0b s0p
 let s0b_s0c := ppt s0b s0c
 s0b.name = "bake-01" ∧
 PAG s0b_s0p s0b s0p ∧
 PPT s0b_s0c s0b s0c ∧
 s0p.name = "person" ∧
 s0c.name = "cake"

-- [Optional knowledge insertion point: extra axioms may be added here if needed]


-- natural language description: A cake was baked.
theorem thm_bake_01_s1b :
 ∃ s1b : Event,
 ∃ s1c : Entity,
 let s1b_s1c := ppt s1b s1c
 s1b.name = "bake-01" ∧
 PPT s1b_s1c s1b s1c ∧
 s1c.name = "cake" := by
  sorry