import tactic

#explode and_iff_left

-- Colocando el cursor sobre explode se obtiene
--    and_iff_left : ∀ {a b : Prop}, b → (a ∧ b ↔ a)
--    0 │   │ a         ├ Prop
--    1 │   │ b         ├ Prop
--    2 │   │ hb        ├ b
--    3 │   │ and.left  │ a ∧ b → a
--    4 │   │ ha        │ ┌ a
--    5 │4,2│ and.intro │ │ a ∧ b
--    6 │4,5│ ∀I        │ a → a ∧ b
--    7 │3,6│ iff.intro │ a ∧ b ↔ a
--    8 │2,7│ ∀I        │ b → (a ∧ b ↔ a)
--    9 │1,8│ ∀I        │ ∀ {b : Prop}, b → (a ∧ b ↔ a)
--    10│0,9│ ∀I        │ ∀ {a b : Prop}, b → (a ∧ b ↔ a)
