import order.lattice

meta def infs_and_sups :=
`[refl <|> 
  {apply inf_le_left_of_le, infs_and_sups} <|> 
  {apply inf_le_right_of_le, infs_and_sups} <|>
  {apply le_sup_left_of_le, infs_and_sups} <|> 
 {apply le_sup_right_of_le, infs_and_sups}]

meta def tactic.interactive.lattice :=
`[try { apply le_antisymm }; 
        repeat { apply le_inf <|> 
                 apply sup_le }; 
        infs_and_sups]

variables {L : Type*} [lattice L] {a b c x y z : L}

example : a ⊔ (b ⊓ c) ≤ (a ⊔ b) ⊓ (a ⊔ c) :=
by lattice

example : a ⊔ (a ⊓ b) = a :=
by lattice

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
by lattice

example : x ⊓ y = y ⊓ x :=
by lattice

-- 2ª solución
-- ===========

meta def tactic.interactive.lattice2 :=
`[solve_by_elim
  [le_antisymm, 
   le_inf, 
   sup_le, 
   le_refl, 
   inf_le_left_of_le, 
   inf_le_right_of_le,
   le_sup_left_of_le, 
   le_sup_right_of_le]
  {max_depth := 30}]

example : a ⊔ (b ⊓ c) ≤ (a ⊔ b) ⊓ (a ⊔ c) :=
by lattice2

example : a ⊔ (a ⊓ b) = a :=
by lattice2

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
by lattice2

example : x ⊓ y = y ⊓ x :=
by lattice2
