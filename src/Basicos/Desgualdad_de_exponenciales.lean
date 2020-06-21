import analysis.special_functions.exp_log

open real

#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)

example (a b : ℝ) (h : a ≤ b) : exp a ≤ exp b :=
begin
  rw exp_le_exp,
  exact h
end
