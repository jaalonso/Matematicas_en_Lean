-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que en los retículos se verifica que
--    x ⊔ y) ⊔ z = x ⊔ (y ⊔ z)
-- ---------------------------------------------------------------------

import order.lattice

variables {α : Type*} [lattice α]
variables x y z : α

-- 1ª demostración
-- ===============

example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
begin
  apply le_antisymm,
  { apply sup_le,
    { apply sup_le le_sup_left (le_sup_right_of_le le_sup_left)},
    { apply le_sup_right_of_le le_sup_right}},
  { apply sup_le,
    { apply le_sup_left_of_le le_sup_left},
    { apply sup_le (le_sup_left_of_le le_sup_right) le_sup_right}},
end

-- Su desarrollo es
--
-- ⊢ x ⊔ y ⊔ z = x ⊔ (y ⊔ z)
--    apply le_antisymm,
-- | ⊢ x ⊔ y ⊔ z ≤ x ⊔ (y ⊔ z)
-- |    { apply sup_le,
-- | | ⊢ x ⊔ y ≤ x ⊔ (y ⊔ z)
-- | |     { apply sup_le le_sup_left (le_sup_right_of_le le_sup_left)},
-- | | ⊢ z ≤ x ⊔ (y ⊔ z)
-- | |     { apply le_sup_right_of_le le_sup_right}},
-- | ⊢ x ⊔ (y ⊔ z) ≤ x ⊔ y ⊔ z
-- |    { apply sup_le,
-- | | ⊢ x ≤ x ⊔ y ⊔ z
-- | |      { apply le_sup_left_of_le le_sup_left},
-- | | ⊢ y ⊔ z ≤ x ⊔ y ⊔ z
-- | |      { apply sup_le (le_sup_left_of_le le_sup_right) le_sup_right}},
-- no goals

-- 2ª demostración
-- ===============

example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
le_antisymm
  (sup_le
    (sup_le le_sup_left (le_sup_right_of_le le_sup_left))
    (le_sup_right_of_le le_sup_right))
  (sup_le
    (le_sup_left_of_le le_sup_left)
    (sup_le (le_sup_left_of_le le_sup_right) le_sup_right))

-- 3ª demostración
-- ===============

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := 
sup_assoc
