-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que en los retículos se verifica que
--     x ⊓ y = y ⊓ x
-- ----------------------------------------------------------------------

import order.lattice

variables {α : Type*} [lattice α]
variables x y z : α

-- 1ª demostración
-- ===============

lemma aux : x ⊓ y ≤ y ⊓ x :=
begin
  apply le_inf,
  apply inf_le_right,
  apply inf_le_left,
end

-- Su desarrollo es
--
-- ⊢ x ⊓ y ≤ y ⊓ x
--    apply le_inf,
-- ⊢ x ⊓ y ≤ y
-- |   apply inf_le_right,
-- ⊢ x ⊓ y ≤ y
-- |   apply inf_le_left,
-- no goals

example : x ⊓ y = y ⊓ x :=
begin
  apply le_antisymm,
  apply aux,
  apply aux,
end

-- Su desarrollo es
--
-- ⊢ x ⊓ y = y ⊓ x
--    apply le_antisymm,
-- ⊢ x ⊓ y ≤ y ⊓ x
-- |   apply aux,
-- ⊢ y ⊓ x ≤ x ⊓ y
-- |   apply aux,
-- no goals

-- 2ª demostración
-- ===============

example : x ⊓ y = y ⊓ x :=
by apply le_antisymm; simp

-- 3ª demostración
-- ===============

example : x ⊓ y = y ⊓ x :=
inf_comm

-- Lemas usados
-- ============

-- #check (inf_comm : x ⊓ y = y ⊓ x)
-- #check (inf_le_left : x ⊓ y ≤ x)
-- #check (inf_le_right : x ⊓ y ≤ y)
-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
-- #check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
