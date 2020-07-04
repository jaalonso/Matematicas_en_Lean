import data.real.basic tactic

variables a b : ℝ

example : abs (a*b) ≤ (a^2 + b^2) / 2 :=
begin
  have h3: 0 ≤ (a+b)^2, {exact pow_two_nonneg (a + b)},
  have h5: (0:ℝ) < 2, {exact two_pos},
  have h4: (a+b)^2/2 ≥ 0, {exact div_nonneg h3 h5},
  sorry
end
