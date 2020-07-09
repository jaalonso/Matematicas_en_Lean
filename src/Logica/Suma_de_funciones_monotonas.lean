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
  : monotone (λ x, f x + g x) :=
begin
  intros a b aleb,
  apply add_le_add,
  apply mf aleb,
  apply mg aleb
end

-- Su desarrollo es
-- 
-- f g : ℝ → ℝ,
-- mf : monotone f,
-- mg : monotone g
-- ⊢ monotone (λ (x : ℝ), f x + g x)
--    >> intros a b aleb,
-- a b : ℝ,
-- aleb : a ≤ b
-- ⊢ (λ (x : ℝ), f x + g x) a ≤ (λ (x : ℝ), f x + g x) b
--    >> apply add_le_add,
-- | ⊢ f a ≤ f b
-- |    >> apply mf aleb,
-- | ⊢ g a ≤ g b
-- |    >> apply mg aleb
-- no goals

-- 2ª demostración
-- ===============

example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f x + g x) :=
λ a b aleb, add_le_add (mf aleb) (mg aleb)

-- Nota: Se puede iniciar la prueba con
--    λ a b aleb, _
-- situarse en _, pulsar C-c SPC y elegir library_search. Automáticamente, se
-- completa la prueba.
