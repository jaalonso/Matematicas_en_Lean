-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones
--    1. Importar la teoría de retículos.
--    2. Declarar α como un tipo sobre retículos
--    3. Declarar x e y como variabkes sobre α
-- ----------------------------------------------------------------------

import order.lattice               -- 1
variables {α : Type*} [lattice α]  -- 2
variables x y : α                  -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    x ⊓ (x ⊔ y) = x
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
begin
  have h1 : x ⊓ (x ⊔ y) ≤ x, finish,
  have h2 : x ≤ x ⊓ (x ⊔ y), finish,
  show x ⊓ (x ⊔ y) = x,
    by exact le_antisymm h1 h2,
end

-- 2ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
begin
  have h1 : x ⊓ (x ⊔ y) ≤ x := inf_le_left,
  have h2 : x ≤ x ⊓ (x ⊔ y),
  { have h2a : x ≤ x := rfl.ge,
    have h2b : x ≤ x ⊔ y := le_sup_left,
    show x ≤ x ⊓ (x ⊔ y),
      by exact le_inf h2a h2b, },
  show x ⊓ (x ⊔ y) = x,
    by exact le_antisymm h1 h2,
end

-- 3ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
begin
  apply le_antisymm,
  { apply inf_le_left },
  { apply le_inf,
    { apply le_refl },
    { apply le_sup_left }},
end

-- Su desarrollo es
--
-- ⊢ x ⊓ (x ⊔ y) = x
--    apply le_antisymm,
-- | ⊢ x ⊓ (x ⊔ y) ≤ x
-- | |   { apply inf_le_left },
-- | ⊢ x ≤ x ⊓ (x ⊔ y)
-- |   { apply le_inf,
-- | | ⊢ x ≤ x
-- | |     { apply le_refl },
-- | | ⊢ x ≤ x ⊔ y
-- | |     { apply le_sup_left }},
-- no goals

-- 4ª demostración
example : x ⊓ (x ⊔ y) = x :=
-- by library_search
inf_sup_self

-- 5ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x :=
-- by hint
by simp

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--    x ⊔ (x ⊓ y) = x
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
begin
  have h1 : x ⊔ (x ⊓ y) ≤ x, finish,
  have h2 : x ≤ x ⊔ (x ⊓ y), finish,
  show x ⊔ (x ⊓ y) = x,
    by exact le_antisymm h1 h2,
end

-- 2ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
begin
  have h1 : x ⊔ (x ⊓ y) ≤ x,
  { have h1a : x ≤ x := le_rfl,
    have h1b : x ⊓ y ≤ x := inf_le_left,
    show x ⊔ (x ⊓ y) ≤ x,
      by exact sup_le h1a h1b,
  },
  have h2 : x ≤ x ⊔ (x ⊓ y) := le_sup_left,
  show x ⊔ (x ⊓ y) = x,
    by exact le_antisymm h1 h2,
end

-- 3ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
begin
  apply le_antisymm,
  { apply sup_le,
    { apply le_refl },
    { apply inf_le_left }},
  { apply le_sup_left },
end

-- Su desarrollo es
--
-- ⊢ x ⊔ x ⊓ y = x
--    apply le_antisymm,
-- | ⊢ x ⊔ x ⊓ y ≤ x
-- |    { apply sup_le,
-- | | ⊢ x ≤ x
-- | |      { apply le_refl },
-- | | ⊢ x ⊓ y ≤ x
-- | |      { apply inf_le_left }},
-- | ⊢ x ≤ x ⊔ x ⊓ y
-- | |    { apply le_sup_left },
-- no goals

-- 4ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
-- by library_search
sup_inf_self

-- 4ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x :=
-- by hint
by simp
