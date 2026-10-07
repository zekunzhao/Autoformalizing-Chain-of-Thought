axiom Bird : Type
axiom CanFly : Bird → Prop
axiom Tweety : Bird
axiom AllBirdsFly : ∀ b : Bird, CanFly b

theorem tweety_flies : CanFly Tweety := by
  sorry
