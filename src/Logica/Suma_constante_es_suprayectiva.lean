-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que para todo número real c, la función
--    f(x) x  + c
-- es suprayectiva. 
-- ----------------------------------------------------------------------

import data.real.basic

variable {c : ℝ} 

open function

-- 1ª demostración
-- ===============

example : surjective (λ x, x + c) :=
begin
  intro x,
  use x - c,
  dsimp, 
  ring,
end

-- Su desarrollo es
-- 
-- c : ℝ
-- ⊢ surjective (λ (x : ℝ), x + c)
--    >> intro x,
-- ⊢ ∃ (a : ℝ), (λ (x : ℝ), x + c) a = x
--    >> use x - c,
-- ⊢ (λ (x : ℝ), x + c) (x - c) = x
--    >> dsimp,
-- ⊢ x - c + c = x 
--    >> ring,
-- no goals

-- 2ª demostración
-- ===============

example : surjective (λ x, x + c) :=
begin
  intro x,
  use x - c,
  change (x - c) + c = x,
  ring,
end

-- Su desarrollo es
-- 
-- c : ℝ
-- ⊢ surjective (λ (x : ℝ), x + c)
--    >> intro x,
-- ⊢ ∃ (a : ℝ), (λ (x : ℝ), x + c) a = x
--    >> use x - c,
-- ⊢ (λ (x : ℝ), x + c) (x - c) = x
--    >> change (x - c) + c = x,
-- ⊢ x - c + c = x
--    >> ring,
-- no goals
