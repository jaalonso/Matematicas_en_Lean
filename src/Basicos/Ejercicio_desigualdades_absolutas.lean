import data.real.basic tactic

variables a b : ℝ

example : abs (a*b) ≤ (a^2 + b^2) / 2 :=
sorry

-- Los lemas usados son:
#check (abs_le_of_le_of_neg_le : a ≤ b → -a ≤ b → abs a ≤ b)
