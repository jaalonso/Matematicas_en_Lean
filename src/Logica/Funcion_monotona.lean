-- ---------------------------------------------------------------------
-- Ejercicio. Explicitar la definición de función monótona poniendo el
-- nombre en la hipótesis y su definición en la conclusión. 
-- ----------------------------------------------------------------------

import data.real.basic

example 
  (f : ℝ → ℝ) 
  (h : monotone f) :
  ∀ {a b}, a ≤ b → f a ≤ f b := h
