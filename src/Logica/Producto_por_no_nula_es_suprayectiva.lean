-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si c es un número real no nulo, entonces la
-- función 
--    f(x) = c * x
-- es suprayectiva. 
-- ----------------------------------------------------------------------

import data.real.basic

open function

example 
  {c : ℝ} 
  (h : c ≠ 0) 
  : surjective (λ x, c * x) :=
begin
  intro x,
  use (x / c),
  change c * (x / c) = x,
  rw mul_comm,
  apply div_mul_cancel,
  exact h,
end

-- Su prueba es
-- 
-- c : ℝ,
-- h : c ≠ 0
-- ⊢ surjective (λ (x : ℝ), c * x)
--    >> intro x,
-- x : ℝ
-- ⊢ ∃ (a : ℝ), (λ (x : ℝ), c * x) a = x
--    >> use (x / c),
-- ⊢ (λ (x : ℝ), c * x) (x / c) = x
--    >> change c * (x / c) = x,
-- ⊢ c * (x / c) = x
--    >> rw mul_comm,
-- ⊢ x / c * c = x
--    >> apply div_mul_cancel,
-- ⊢ c ≠ 0
--    >> exact h,
-- no goals
