-- ---------------------------------------------------------------------
-- Ejercicio. Sean a, b, y c números reales. Demostrar  que si
--    1 ≤ a
--    b ≤ c
-- entonces
--    2 + a + exp b ≤ 3 * a + exp c
-- ----------------------------------------------------------------------

import analysis.special_functions.log.basic

open real

variables a b c : ℝ

example
  (h  : 1 ≤ a)
  (h' : b ≤ c)
  : 2 + a + exp b ≤ 3 * a + exp c :=
by linarith [exp_le_exp.mpr h']
