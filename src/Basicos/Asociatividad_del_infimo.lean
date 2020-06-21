import order.lattice

variables {α : Type*} [lattice α]
variables x y z : α

-- 1ª demostración
-- ===============

-- 1ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) := 
le_antisymm
  (le_inf
    (inf_le_left_of_le inf_le_left)
    (le_inf (inf_le_left_of_le inf_le_right) inf_le_right))
  (le_inf
    (le_inf inf_le_left (inf_le_right_of_le inf_le_left))
    (inf_le_right_of_le inf_le_right))

-- 2ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) := 
inf_assoc

