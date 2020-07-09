-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si c es no negativo y f es monótona,
-- entonces c * f es monótona.
-- ----------------------------------------------------------------------

import data.real.basic

variables (f : ℝ → ℝ)

-- 1ª demostración
-- ===============

example 
  {c : ℝ}       
  (mf : monotone f) 
  (nnc : 0 ≤ c) 
  : monotone (λ x, c * f x) :=
begin 
  intros a b aleb,
  apply mul_le_mul_of_nonneg_left,
  apply mf aleb,
  apply nnc
end

-- Su desarrollo es
-- 
-- f : ℝ → ℝ,
-- c : ℝ,
-- mf : monotone f,
-- nnc : 0 ≤ c
-- ⊢ monotone (λ (x : ℝ), c * f x)
--    >> intros a b aleb,
-- a b : ℝ,
-- aleb : a ≤ b
-- ⊢ (λ (x : ℝ), c * f x) a ≤ (λ (x : ℝ), c * f x) b
--    >> apply mul_le_mul_of_nonneg_left,
-- | ⊢ f a ≤ f b
-- |    >> apply mf aleb,
-- | ⊢ 0 ≤ c
-- |    >> apply nnc
-- no goals

-- 2ª demostración
-- ===============

example {c : ℝ} (mf : monotone f) (nnc : 0 ≤ c) :
  monotone (λ x, c * f x) :=
λ a b aleb, mul_le_mul_of_nonneg_left (mf aleb) nnc

