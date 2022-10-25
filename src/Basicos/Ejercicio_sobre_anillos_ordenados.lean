-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones
--    1. Importar la teoría de los anillos ordenados.
--    2. Declarar R como un tipo sobre los anillos ordenados.
--    3. Declarar a, b y c como variables sobre R.
-- ----------------------------------------------------------------------

import algebra.order.ring                -- 1
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
    0   = a - a : (sub_self a).symm
    ... ≤ b - a : sub_le_sub_right h a
end

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--    0 ≤ b - a → a ≤ b
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : 0 ≤ b - a → a ≤ b :=
begin
  intro h,
  calc
    a   = 0 + a       : (zero_add a).symm
    ... ≤ (b - a) + a : add_le_add_right h a
    ... = b           : sub_add_cancel b a
end

-- 2ª demostración
-- ===============

example : 0 ≤ b - a → a ≤ b :=
-- by library_search
sub_nonneg.mp

-- 3ª demostración
-- ===============

example : 0 ≤ b - a → a ≤ b :=
-- by hint
by simp

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que
--    a ≤ b
--    0 ≤ c
-- entonces
--    a * c ≤ b * c
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
begin
  have h3 : 0 ≤ b - a :=
    sub_nonneg.mpr h1,
  have h4 : 0 ≤ (b - a) * c :=
    mul_nonneg h3 h2,
  have h5 : (b - a) * c = b * c - a * c :=
    sub_mul b a c,
  have h6 : 0 ≤ b * c - a * c :=
    eq.trans_ge h5 h4,
  show a * c ≤ b * c,
    by exact sub_nonneg.mp h6,
end

-- 2ª demostración
-- ===============

open_locale classical

example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
begin
  by_cases h3 : b ≤ a,
  { have h3a : a = b :=
      le_antisymm h1 h3,
    show a * c ≤ b * c,
      by rw h3a },
  { by_cases h4 : c = 0,
    { calc a * c = a * 0 : by rw h4
             ... = 0     : by rw mul_zero
             ... ≤ 0     : le_refl 0
             ... = b * 0 : by rw mul_zero
             ... = b * c : by {congr ; rw h4}},
    { apply le_of_lt,
      apply mul_lt_mul_of_pos_right,
      { show a < b,
          by exact lt_of_le_not_le h1 h3 },
      { show 0 < c,
          by exact lt_of_le_of_ne h2 (ne.symm h4) }}},
end

-- 3ª demostración
example
  (h1 : a ≤ b)
  (h2 : 0 ≤ c)
  : a * c ≤ b * c :=
-- by library_search
mul_le_mul_of_nonneg_right h1 h2
