-- ---------------------------------------------------------------------
-- Ejercicio. Sean a, b, c, d y e números reales. Demostrar que si 
-- d ≤ e, entonces
--    c + exp (a + d) ≤ c + exp (a + e)
-- ---------------------------------------------------------------------

import analysis.special_functions.exp_log

open real

variables (a b c d e : ℝ)

-- 1ª demostración
-- ===============
 
example 
  (h₀ : d ≤ e) 
  : c + exp (a + d) ≤ c + exp (a + e) :=
begin
  suffices h: exp (a + d) ≤ exp (a + e), {linarith},
  apply exp_le_exp.mpr,
  exact add_le_add_left h₀ a,
end

-- 2ª demostración
-- ===============
 
@[mono] 
lemma exp_le_exp' 
  {x y : ℝ} 
  : x ≤ y → exp x ≤ exp y := 
exp_le_exp.mpr

example 
  (h₀ : d ≤ e) 
  : c + exp (a + d) ≤ c + exp (a + e) :=
by mono*





