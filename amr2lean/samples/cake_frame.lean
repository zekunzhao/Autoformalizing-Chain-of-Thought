structure Entity where
  name : String

structure Prep where
  name : String

structure bake_01_s1b where
  (arg0 : Option Entity) -- PAG
  (arg1 : Option Entity) -- PPT
  (arg2 : Option Entity) -- VSP
  (arg3 : Option Entity) -- GOL

structure bake_01_s2b where
  (arg0 : Option Entity) -- PAG
  (arg1 : Option Entity) -- PPT
  (arg2 : Option Entity) -- VSP
  (arg3 : Option Entity) -- GOL

-- natural language description: Someone baked a cake.
axiom ax_s1_s1b:
 ∃ s1b : bake_01_s1b,
 ∃ s1p : Entity,
 ∃ s1c : Entity,
 s1p.name = "person" ∧
 s1c.name = "cake" ∧
 s1b = { arg0 := some s1p, arg1 := some s1c, arg2 := none, arg3 := none }

-- natural language description: A cake was baked.
-- [Optional knowledge insertion point: extra axioms may be added here if needed]

theorem thm_s2_s2b:
 ∃ s2b : bake_01_s2b,
 ∃ s2c : Entity,
 s2c.name = "cake" ∧
 s2b = { arg0 := none, arg1 := some s2c, arg2 := none, arg3 := none }
:= by
  sorry