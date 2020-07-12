-- ---------------------------------------------------------------------
-- Ejercicio. Sea x un número real tal que para todo número positivo ε,
-- x ≤ ε Demostrar que x ≤ 0.
-- ----------------------------------------------------------------------


import data.real.basic

-- 1ª demostración
-- ===============

example 
  (x : ℝ) 
  (h : ∀ ε > 0, x ≤ ε) 
  : x ≤ 0 :=
begin
  apply le_of_not_gt,
  intro hx0,
  specialize h (x/2),
  have h1 : x ≤ x / 2,
    { apply h,
      apply half_pos hx0},
  have : x / 2 < x,
    { apply half_lt_self hx0 },
  linarith,
end

-- Prueba
-- ======

-- x : ℝ,
-- h : ∀ (ε : ℝ), ε > 0 → x ≤ ε
-- ⊢ x ≤ 0
--    >> apply le_of_not_gt,
-- ⊢ ¬x > 0
--    >> intro hx0,
-- hx0 : x > 0
-- ⊢ false
--    >> specialize h (x/2),
-- h : x / 2 > 0 → x ≤ x / 2
-- ⊢ false
--    >> have h1 : x ≤ x / 2,
--    >>   { apply h,
-- ⊢ x / 2 > 0
--    >>     apply half_pos hx0},
-- h1 : x ≤ x / 2
-- ⊢ false
--    >> have : x / 2 < x,
--    >>   { apply half_lt_self hx0 },
-- this : x / 2 < x
-- ⊢ false
--    >> linarith,
-- no goals

-- 2ª demostración
-- ===============

example 
  (x : ℝ) 
  (h : ∀ ε > 0, x ≤ ε) 
  : x ≤ 0 :=
begin
  contrapose! h,
  use x / 2,
  split; linarith,
end

-- Prueba
-- ======

-- x : ℝ,
-- h : ∀ (ε : ℝ), ε > 0 → x ≤ ε
-- ⊢ x ≤ 0
--    >> contrapose! h,
-- h : 0 < x
-- ⊢ ∃ (ε : ℝ), ε > 0 ∧ ε < x
--    >> use x / 2,
-- ⊢ x / 2 > 0 ∧ x / 2 < x
--    >> split; linarith
-- no goals

