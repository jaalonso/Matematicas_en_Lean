-- ---------------------------------------------------------------------
-- Ejercicio. Sean a y b números reales. Demostrar que
--    abs (a*b) ≤ (a^2 + b^2) / 2 :=
-- ----------------------------------------------------------------------

import data.real.basic 

variables a b : ℝ

example : abs (a*b) ≤ (a^2 + b^2) / 2 :=
begin
  apply abs_le_of_le_of_neg_le,
  { have h1 : 0 ≤ a^2 - 2*a*b + b^2,
      calc 0 ≤ (a-b)^2                : by exact pow_two_nonneg (a - b)
         ... = a^2-2*a*b+b^2          : by ring,
    have h2 : 2*(a*b) ≤ a^2 + b^2,
      calc 2*(a*b) 
           ≤ 2*(a*b)+(a^2-2*a*b+b^2)  : by exact le_add_of_nonneg_right h1
       ... = a^2 + b^2                : by ring,
    by linarith [h2] },
  { have h3 : 0 ≤ a^2 + 2*a*b + b^2,
      calc 0 ≤ (a+b)^2                : by exact pow_two_nonneg (a + b)
         ... = a^2+2*a*b+b^2          : by ring,
    have h4 : -2*(a*b) ≤ a^2 + b^2,
      calc -2*(a*b) 
           ≤ -2*(a*b)+(a^2+2*a*b+b^2) : by exact le_add_of_nonneg_right h3
       ... = a^2 + b^2                : by ring,
    by linarith [h4] },
end
