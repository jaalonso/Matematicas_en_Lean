import analysis.special_functions.exp_log

open real

variables a b c d e : ℝ

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) :=
begin
  apply add_le_add,
  apply le_refl,
  apply exp_le_exp.mpr,
  apply add_le_add,
  apply le_refl,
  exact h₀,
end

example : (0 : ℝ) < 1 :=
by norm_num

-- Nota: La táctica norm_num normaliza expresiones numéricas. Ver 
-- https://bit.ly/3hoJMgQ

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) :=
begin
  have h₀ : 0 < 1 + exp a,
  { apply add_pos,
    norm_num,
    apply exp_pos },
  have h₁ : 0 < 1 + exp b,
  { apply add_pos,
    norm_num,
    apply exp_pos },
  apply (log_le_log h₀ h₁).mpr,
  apply add_le_add,
  apply le_refl,
  apply exp_le_exp.mpr h,
end

-- Los lemas empleados son
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (le_refl : ∀ (a : real), a ≤ a)
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check (log_le_log : 0 < a → 0 < b → (log a ≤ log b ↔ a ≤ b))
