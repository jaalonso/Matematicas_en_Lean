-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la función identidad no está acotada
-- superiormente. 
-- ----------------------------------------------------------------------


import .Funcion_no_acotada_superiormente

example : ¬ fn_has_ub (λ x, x) :=
begin
  apply no_has_ub,
  intro a,
  use a + 1,
  linarith,
end

-- Prueba
-- ------

-- ⊢ ¬fn_has_ub (λ (x : ℝ), x)
--    >> apply no_has_ub,
-- ⊢ ∀ (a : ℝ), ∃ (x : ℝ), x > a
--    >> intro a,
-- a : ℝ
-- ⊢ ∃ (x : ℝ), x > a
--    >> use a + 1,
-- ⊢ a + 1 > a
--    >> linarith,
-- no goals
