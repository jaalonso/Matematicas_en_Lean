-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si c es no negativo y f es monótona,
-- entonces c * f es monótona.
-- ----------------------------------------------------------------------

import data.real.basic

variables (f : ℝ → ℝ)
variable  {c : ℝ}

-- 1ª demostración
-- ===============

example
  (mf : monotone f)
  (nnc : 0 ≤ c)
  : monotone (λ x, c * f x) :=
begin
  have h1 : ∀ a b, a ≤ b → (λ x, c * f x) a ≤ (λ x, c * f x) b,
    { intros a b hab,
      have h2 : f a ≤ f b := mf hab,
      have h3 : c * f a ≤ c * f b := mul_le_mul_of_nonneg_left h2 nnc,
      show (λ x, c * f x) a ≤ (λ x, c * f x) b,
        by exact h3, },
  show monotone (λ x, c * f x),
    by exact h1,
end

-- 2ª demostración
-- ===============

example
  (mf : monotone f)
  (nnc : 0 ≤ c)
  : monotone (λ x, c * f x) :=
begin
  intros a b hab,
  apply mul_le_mul_of_nonneg_left,
  apply mf hab,
  apply nnc
end

-- Su desarrollo es
--
-- f : ℝ → ℝ,
-- c : ℝ,
-- mf : monotone f,
-- nnc : 0 ≤ c
-- ⊢ monotone (λ (x : ℝ), c * f x)
--    >> intros a b hab,
-- a b : ℝ,
-- hab : a ≤ b
-- ⊢ (λ (x : ℝ), c * f x) a ≤ (λ (x : ℝ), c * f x) b
--    >> apply mul_le_mul_of_nonneg_left,
-- | ⊢ f a ≤ f b
-- |    >> apply mf hab,
-- | ⊢ 0 ≤ c
-- |    >> apply nnc
-- no goals

-- 3ª demostración
-- ===============

example (mf : monotone f) (nnc : 0 ≤ c) :
  monotone (λ x, c * f x) :=
λ a b hab, mul_le_mul_of_nonneg_left (mf hab) nnc
