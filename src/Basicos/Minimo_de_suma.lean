-- ---------------------------------------------------------------------
-- Ejercicio. Sean a, b y c números reales. Demostrar que
--    min a b + c = min (a + c) (b + c)
-- ----------------------------------------------------------------------

import data.real.basic

variables a b c : ℝ

example : min a b + c = min (a + c) (b + c) :=
begin
  by_cases (a ≤ b),
  { have h1 : a + c ≤ b + c,
      apply add_le_add_right h,
    calc min a b + c = a + c               : by simp [min_eq_left h]
                 ... = min (a + c) (b + c) : by simp [min_eq_left h1]},
  { have h2: b ≤ a,
      linarith,
    have h3 : b + c ≤ a + c,
      { exact add_le_add_right h2 c },
    calc min a b + c = b + c               : by simp [min_eq_right h2]
                 ... = min (a + c) (b + c) : by simp [min_eq_right h3]},
end
