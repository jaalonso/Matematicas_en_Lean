-- ---------------------------------------------------------------------
-- Ejercicio. Sean a, b, y d números reales. Demostrar  que si
--    1 ≤ a
--    b ≤ d
-- entonces
--    2 + a + exp b ≤ 3 * a + exp d
-- ----------------------------------------------------------------------

import analysis.special_functions.log.basic

open real

variables a b d : ℝ

example
  (h  : 1 ≤ a)
  (h' : b ≤ d)
  : 2 + a + exp b ≤ 3 * a + exp d :=
by linarith [exp_le_exp.mpr h']
