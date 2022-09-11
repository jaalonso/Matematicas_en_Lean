-- ---------------------------------------------------------------------
-- Ejercicio. Sean a y b números reales. Demostrar que
--    2*a*b ≤ a^2 + b^2
-- ----------------------------------------------------------------------

import data.real.basic
import tactic

variables a b : ℝ

-- 1ª demostración
example : 2*a*b ≤ a^2 + b^2 :=
begin
  have : 0 ≤ (a - b)^2 := pow_two_nonneg (a - b),
  have : 0 ≤ a^2 - 2*a*b + b^2, by linarith,
  show 2*a*b ≤ a^2 + b^2, by linarith,
end

-- 2ª demostración
example : 2*a*b ≤ a^2 + b^2 :=
begin
  have h : 0 ≤ a^2 - 2*a*b + b^2,
  { calc a^2 - 2*a*b + b^2
        = (a - b)^2                   : by ring
    ... ≥ 0                           : by apply pow_two_nonneg },
  calc 2*a*b
       = 2*a*b + 0                   : by ring
   ... ≤ 2*a*b + (a^2 - 2*a*b + b^2) : add_le_add (le_refl _) h
   ... = a^2 + b^2                   : by ring
end

-- 3ª demostración
example : 2*a*b ≤ a^2 + b^2 :=
begin
  have : 0 ≤ a^2 - 2*a*b + b^2,
  { calc a^2 - 2*a*b + b^2
         = (a - b)^2       : by ring
     ... ≥ 0               : by apply pow_two_nonneg },
  linarith,
end

-- 4ª demostración
example : 2*a*b ≤ a^2 + b^2 :=
-- by library_search
two_mul_le_add_sq a b
