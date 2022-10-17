-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que en los retículos se verifica que
--     x ⊔ y = y ⊔ x
-- ----------------------------------------------------------------------

import order.lattice

variables {α : Type*} [lattice α]
variables x y z : α

-- 1ª demostración
-- ===============

lemma aux1 : x ⊔ y ≤ y ⊔ x :=
begin
  have h1 : x ≤ y ⊔ x,
    by exact le_sup_right,
  have h2 : y ≤ y ⊔ x,
    by exact le_sup_left,
  show x ⊔ y ≤ y ⊔ x,
    by exact sup_le h1 h2,
end

example : x ⊔ y = y ⊔ x :=
begin
  have h1 : x ⊔ y ≤ y ⊔ x,
    by exact aux1 x y,
  have h2 : y ⊔ x ≤ x ⊔ y,
    by exact aux1 y x,
  show x ⊔ y = y ⊔ x,
    by exact le_antisymm h1 h2,
end

-- 2ª demostración
-- ===============

lemma aux2 : x ⊔ y ≤ y ⊔ x :=
sup_le le_sup_right le_sup_left

example : x ⊔ y = y ⊔ x :=
le_antisymm (aux2 x y) (aux2 y x)

-- 3ª demostración
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

-- 4ª demostración
-- ===============

example : x ⊔ y = y ⊔ x :=
by apply le_antisymm; simp

-- 5ª demostración
-- ===============

example : x ⊔ y = y ⊔ x :=
-- by library_search
sup_comm

-- 6ª demostración
-- ===============

example : x ⊔ y = y ⊔ x :=
-- by hint
by finish

-- Lemas usados
-- ============

-- #check (sup_comm : x ⊔ y = y ⊔ x)
-- #check (le_sup_left : x ≤ x ⊔ y)
-- #check (le_sup_right : y ≤ x ⊔ y)
-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
-- #check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
