-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que en los retículos se verifica que
--     (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z)
-- ----------------------------------------------------------------------

import order.lattice

variables {α : Type*} [lattice α]
variables x y z : α

-- 1ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) := 
begin
  apply le_antisymm,
  { apply le_inf,
    { apply inf_le_left_of_le inf_le_left, },
    { apply le_inf (inf_le_left_of_le inf_le_right) inf_le_right}},
  {apply le_inf,
    { apply le_inf inf_le_left (inf_le_right_of_le inf_le_left), },
    { apply inf_le_right_of_le inf_le_right, },},
end

-- Su desarrollo es
--
-- ⊢ x ⊓ y ⊓ z = x ⊓ (y ⊓ z)
--    apply le_antisymm,
-- ⊢ x ⊓ y ⊓ z ≤ x ⊓ (y ⊓ z)
-- |   { apply le_inf,
-- | ⊢ x ⊓ y ⊓ z ≤ x
-- | |     { apply inf_le_left_of_le inf_le_left },
-- | ⊢ x ⊓ y ⊓ z ≤ y ⊓ z
-- | |     { apply le_inf (inf_le_left_of_le inf_le_right) inf_le_right}},
-- ⊢ x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z
-- |   {apply le_inf,
-- | ⊢ x ⊓ (y ⊓ z) ≤ x ⊓ y
-- | |     { apply le_inf inf_le_left (inf_le_right_of_le inf_le_left)},
-- | ⊢ x ⊓ (y ⊓ z) ≤ z
--      { apply inf_le_right_of_le inf_le_right, },},
-- no goals

-- 2ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) := 
le_antisymm
  (le_inf
    (inf_le_left_of_le inf_le_left)
    (le_inf (inf_le_left_of_le inf_le_right) inf_le_right))
  (le_inf
    (le_inf inf_le_left (inf_le_right_of_le inf_le_left))
    (inf_le_right_of_le inf_le_right))

-- 3ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) := 
inf_assoc

