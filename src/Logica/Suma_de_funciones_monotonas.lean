-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la suma de dos funciones monótonas es
-- monótona.
-- ----------------------------------------------------------------------

import data.real.basic

variables (f g : ℝ → ℝ)

-- 1ª demostración
-- ===============

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f + g) :=
begin
  have h1 : ∀ a b, a ≤ b → (f + g) a ≤ (f + g ) b,
    { intros a b hab,
      have h2 : f a ≤ f b := mf hab,
      have h3 : g a ≤ g b := mg hab,
      calc (f + g) a
           = f a + g a : rfl
       ... ≤ f b + g b : add_le_add h2 h3
       ... = (f + g) b : rfl, },
  show monotone (f + g),
    by exact h1,
end

-- 2ª demostración
-- ===============

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f + g) :=
begin
  intros a b hab,
  apply add_le_add,
  apply mf hab,
  apply mg hab
end

-- Su desarrollo es
--
-- f g : ℝ → ℝ,
-- mf : monotone f,
-- mg : monotone g
-- ⊢ monotone (λ (x : ℝ), f x + g x)
--    >> intros a b hab,
-- a b : ℝ,
-- hab : a ≤ b
-- ⊢ (λ (x : ℝ), f x + g x) a ≤ (λ (x : ℝ), f x + g x) b
--    >> apply add_le_add,
-- | ⊢ f a ≤ f b
-- |    >> apply mf hab,
-- | ⊢ g a ≤ g b
-- |    >> apply mg hab
-- no goals

-- 3ª demostración
-- ===============

example
  (mf : monotone f)
  (mg : monotone g)
  : monotone (f + g) :=
λ a b hab, add_le_add (mf hab) (mg hab)

-- Nota: Se puede iniciar la prueba con
--    λ a b hab, _
-- situarse en _, pulsar C-c SPC y elegir library_search. Automáticamente, se
-- completa la prueba.
