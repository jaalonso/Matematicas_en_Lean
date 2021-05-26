-- ---------------------------------------------------------------------
-- Ejercicio. Sean a y b números reales. Demostrar que
--    min a b = min b a
-- ----------------------------------------------------------------------

import data.real.basic

variables a b c : ℝ

-- 1ª demostración
-- ===============

example : min a b = min b a :=
begin
  apply le_antisymm,
  { show min a b ≤ min b a,
    apply le_min,
    { apply min_le_right },
    apply min_le_left },
  { show min b a ≤ min a b,
    apply le_min,
    { apply min_le_right },
    apply min_le_left }
end

-- Nota: Se usa "show" para indicar lo que se demuestra en cada bloque.

-- El desarrollo de la prueba es
--
--    ⊢ min a b = min b a
-- apply le_antisymm,
-- |    ⊢ min a b ≤ min b a
-- | apply le_min,
-- | |    ⊢ min a b ≤ b
-- | | { apply min_le_right },
-- | |    ⊢ min a b ≤ a
-- | apply min_le_left,
-- |    ⊢ min b a ≤ min a b
-- | apply le_min,
-- | |    ⊢ min b a ≤ a
-- | { apply min_le_right },
-- | |    ⊢ min b a ≤ b
-- | apply min_le_left }
--    no goals

-- 2ª demostración (con lema local)
-- ================================

example : min a b = min b a :=
begin
  have h : ∀ x y, min x y ≤ min y x,
  { intros x y,
    apply le_min,
    apply min_le_right,
    apply min_le_left },
  apply le_antisymm, apply h, apply h
end

-- Nota: La táctica "intros" introduce las variables en el contexto. Ver
-- https://bit.ly/2UF1EdL

-- 3ª demostración (con repeat)
-- ============================

example : min a b = min b a :=
begin
  apply le_antisymm,
  repeat {
    apply le_min,
    apply min_le_right,
    apply min_le_left },
end

-- Nota. La táctica "repeat" aplica una táctica recursivamente a todos los
-- subobjetivos. Ver https://bit.ly/2YuO5P9

-- Lemas usados
-- ============

-- #check (le_antisymm : a ≤ b → b ≤ a → a = b)
-- #check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
-- #check (min_le_left a b : min a b ≤ a)
-- #check (min_le_right a b : min a b ≤ b)
