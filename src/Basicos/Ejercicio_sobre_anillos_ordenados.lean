-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones
--    1. Importar la teoría de los anillos ordenados.
--    2. Declarar R como un tipo sobre los anillos ordenados.
--    3. Declarar a, b y c como variables sobre R.
-- ----------------------------------------------------------------------

import algebra.ordered_ring              -- 1
variables {R : Type*} [ordered_ring R]   -- 2
variables a b c: R                       -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    a ≤ b → 0 ≤ b - a
-- ----------------------------------------------------------------------

example : a ≤ b → 0 ≤ b - a :=
begin
  intro h,
  calc
    0   = a - a : by rw sub_self
    ... ≤ b - a : sub_le_sub_right h a
end

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--    0 ≤ b - a → a ≤ b
-- ----------------------------------------------------------------------

example : 0 ≤ b - a → a ≤ b :=
begin
  intro h,
  calc
    a   = 0 + a       : by rw zero_add
    ... ≤ (b - a) + a : @add_le_add_right R _ 0 (b -a) h a
    ... = b           : by simp
end

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que
--    a ≤ b
--    0 ≤ c
-- entonces
--    a * c ≤ b * c
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

open_locale classical

example
  (h₁ : a ≤ b)
  (h₂ : 0 ≤ c)
  : a * c ≤ b * c :=
begin
  by_cases h₃ : b ≤ a,
  { have : a = b,
      { apply le_antisymm h₁ h₃},
    rw this },
  { by_cases h₄ : c = 0,
    { calc a * c = a * 0 : by rw h₄
             ... = 0     : by rw mul_zero
             ... ≤ 0     : by exact le_refl 0
             ... = b * 0 : by rw mul_zero
             ... = b * c : by {congr; rw h₄}},
    { apply le_of_lt,
      apply mul_lt_mul_of_pos_right,
      { exact lt_of_le_not_le h₁ h₃ },
      { exact lt_of_le_of_ne h₂ (ne.symm h₄) }}},
end


-- 2ª demostración
example
  (h₁ : a ≤ b)
  (h₂ : 0 ≤ c)
  : a * c ≤ b * c :=
by exact mul_le_mul_of_nonneg_right h₁ h₂

-- 3ª demostración
example
  (h₁ : a ≤ b)
  (h₂ : 0 ≤ c)
  : a * c ≤ b * c :=
mul_le_mul_of_nonneg_right h₁ h₂
