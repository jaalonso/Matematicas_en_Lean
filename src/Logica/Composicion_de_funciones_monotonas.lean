-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la composición de dos funciones monótonas es
-- monótona.
-- ----------------------------------------------------------------------

import data.real.basic

variables (f g : ℝ → ℝ)

-- 1ª demostración
-- ===============

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f ∘ g) :=
begin
  have h1 : ∀ a b, a ≤ b → (f ∘ g) a ≤ (f ∘ g) b,
    { intros a b hab,
      have h1 : g a ≤ g b := mg hab,
      have h2 : f (g a) ≤ f (g b) := mf h1,
      show (f ∘ g) a ≤ (f ∘ g) b,
        by exact h2, },
  show monotone (f ∘ g),
    by exact h1,
end

-- 2ª demostración
-- ===============

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f ∘ g) :=
begin
  intros a b hab,
  apply mf,
  apply mg,
  apply hab
end

-- Su desarrollo es
--
-- f g : ℝ → ℝ,
-- mf : monotone f,
-- mg : monotone g
-- ⊢ monotone (λ (x : ℝ), f (g x))
--    >> intros a b hab,
-- a b : ℝ,
-- hab : a ≤ b
-- ⊢ (λ (x : ℝ), f (g x)) a ≤ (λ (x : ℝ), f (g x)) b
--    >> apply mf,
-- ⊢ g a ≤ g b
--    >> apply mg,
-- ⊢ a ≤ b
--    >> apply hab
-- no goals

-- 3ª demostración
-- ===============

example (mf : monotone f) (mg : monotone g) :
  monotone (f ∘ g) :=
λ a b hab, mf (mg hab)
