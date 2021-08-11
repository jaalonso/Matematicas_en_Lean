-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que en los retículos se verifica que
--     x ⊔ y = y ⊔ x
-- ----------------------------------------------------------------------

import order.lattice

variables {α : Type*} [lattice α]
variables x y z : α

-- 1ª demostración
-- ===============

lemma aux : x ⊔ y ≤ y ⊔ x :=
begin
  apply sup_le,
  apply le_sup_right,
  apply le_sup_left,
end

-- Su desarrollo es
--
-- ⊢ x ⊔ y ≤ y ⊔ x
--    apply sup_le,
-- ⊢ x ≤ y ⊔ x
-- |   apply le_sup_right,
-- ⊢ y ≤ y ⊔ x
-- |   apply le_sup_left,
-- no goals

example : x ⊔ y = y ⊔ x :=
begin
  apply le_antisymm,
  apply aux,
  apply aux,
end

-- Su desarrollo es
--
-- ⊢ x ⊔ y = y ⊔ x
--    apply le_antisymm,
-- ⊢ x ⊔ y ≤ y ⊔ x
-- |   apply aux,
-- ⊢ y ⊔ x ≤ x ⊔ y
-- |   apply aux,
-- no goals

-- 2ª demostración
-- ===============

example : x ⊔ y = y ⊔ x :=
by apply le_antisymm; simp

-- 3ª demostración
-- ===============

example : x ⊔ y = y ⊔ x :=
sup_comm

-- Lemas usados
-- ============

-- #check (sup_comm : x ⊔ y = y ⊔ x)
-- #check (le_sup_left : x ≤ x ⊔ y)
-- #check (le_sup_right : y ≤ x ⊔ y)
-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
-- #check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
