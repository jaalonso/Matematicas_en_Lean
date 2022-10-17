-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que en los retículos se verifica que
--     x ⊓ y = y ⊓ x
-- ----------------------------------------------------------------------

import order.lattice

variables {α : Type*} [lattice α]
variables x y z : α

-- 1ª demostración
-- ===============

lemma aux1 : x ⊓ y ≤ y ⊓ x :=
begin
  have h1 : x ⊓ y ≤ y,
    by exact inf_le_right,
  have h2 : x ⊓ y ≤ x,
    by exact inf_le_left,
  show x ⊓ y ≤ y ⊓ x,
    by exact le_inf h1 h2,
end

example : x ⊓ y = y ⊓ x :=
begin
  have h1 : x ⊓ y ≤ y ⊓ x,
    by exact aux1 x y,
  have h2 : y ⊓ x ≤ x ⊓ y,
    by exact aux1 y x,
  show x ⊓ y = y ⊓ x,
    by exact le_antisymm h1 h2,
end

-- 2ª demostración
-- ===============

lemma aux2 : x ⊓ y ≤ y ⊓ x :=
le_inf inf_le_right inf_le_left

example : x ⊓ y = y ⊓ x :=
le_antisymm (aux2 x y) (aux2 y x)

-- 3ª demostración
-- ===============

lemma aux3 : x ⊓ y ≤ y ⊓ x :=
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
  apply aux3,
  apply aux3,
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

-- 4ª demostración
-- ===============

example : x ⊓ y = y ⊓ x :=
by apply le_antisymm; simp

-- 5ª demostración
-- ===============

example : x ⊓ y = y ⊓ x :=
-- by library_search
inf_comm

-- 6ª demostración
-- ===============

example : x ⊓ y = y ⊓ x :=
-- by hint
by finish

-- Lemas usados
-- ============

-- #check (inf_comm : x ⊓ y = y ⊓ x)
-- #check (inf_le_left : x ⊓ y ≤ x)
-- #check (inf_le_right : x ⊓ y ≤ y)
-- #check (le_antisymm : x ≤ y → y ≤ x → x = y)
-- #check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
