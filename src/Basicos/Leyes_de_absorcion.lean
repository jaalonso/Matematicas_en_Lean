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

-- 2ª demostración
-- ===============

example : x ⊓ (x ⊔ y) = x := 
by simp

-- 3ª demostración
example : x ⊓ (x ⊔ y) = x := 
inf_sup_self

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que 
--    x ⊔ (x ⊓ y) = x
-- ---------------------------------------------------------------------

-- 1ª demostración
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

-- 2ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x := 
by simp

-- 3ª demostración
-- ===============

example : x ⊔ (x ⊓ y) = x := 
sup_inf_self
