-- ---------------------------------------------------------------------
-- Ejercicio. Sean a y b números reales. Demostrar que
--    |a| - |b| ≤ |a - b|
-- ----------------------------------------------------------------------

import data.real.basic

variables a b c : ℝ

example : |a| - |b| ≤ |a - b| :=
calc |a| - |b|
     = |a - b + b| - |b|     : by simp
 ... ≤ (|a - b| + |b|) - |b| : sub_le_sub_right (abs_add (a - b) b) (|b|)
 ... = |a - b|               : add_sub_cancel (|a - b|) (|b|)
