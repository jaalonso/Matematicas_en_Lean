import import analysis.special_functions.exp_log
import tactic

open real

variables a b c : ℝ

-- 1ª demostración
example (h : a ≤ b) : c - exp b ≤ c - exp a :=
begin
   apply add_le_add,
   apply le_refl,
   apply neg_le_neg,
   apply exp_le_exp.mpr h,
end

-- 2ª demostración
example (h : a ≤ b) : c - exp b ≤ c - exp a :=
by linarith [exp_le_exp.mpr h]

-- Los lemas usados son:
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (le_refl : ∀ (a : real), a ≤ a)
#check (neg_le_neg : a ≤ b → -b ≤ -a)
