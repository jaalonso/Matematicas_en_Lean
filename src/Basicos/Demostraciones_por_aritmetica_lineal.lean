-- ---------------------------------------------------------------------
-- Ejercicio 1. Sean a, b, c, d y e números reales. Demostrar que si
--    a ≤ b
--    b < c
--    c ≤ d
--    d < e
-- entonces
--    a < e
-- ----------------------------------------------------------------------

import data.real.basic

variables a b c d e : ℝ

example
  (h₀ : a ≤ b)
  (h₁ : b < c)
  (h₂ : c ≤ d)
  (h₃ : d < e)
  : a < e :=
by linarith

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    2 * a ≤ 3 * b
--    1 ≤ a
--    d = 2
-- entonces
--    d + a ≤ 5 * b
-- ----------------------------------------------------------------------

example
  (h   : 2 * a ≤ 3 * b)
  (h'  : 1 ≤ a)
  (h'' : d = 2)
  : d + a ≤ 5 * b :=
by linarith
