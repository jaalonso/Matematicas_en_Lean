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
  : monotone (λ x, f (g x)) :=
begin
  intros a b aleb,
  apply mf,
  apply mg,
  apply aleb
end

-- Su desarrollo es
--
-- f g : ℝ → ℝ,
-- mf : monotone f,
-- mg : monotone g
-- ⊢ monotone (λ (x : ℝ), f (g x))
--    >> intros a b aleb,
-- a b : ℝ,
-- aleb : a ≤ b
-- ⊢ (λ (x : ℝ), f (g x)) a ≤ (λ (x : ℝ), f (g x)) b
--    >> apply mf,
-- ⊢ g a ≤ g b
--    >> apply mg,
-- ⊢ a ≤ b
--    >> apply aleb
-- no goals

-- 2ª demostración
-- ===============

example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f (g x)) :=
λ a b aleb, mf (mg aleb)
