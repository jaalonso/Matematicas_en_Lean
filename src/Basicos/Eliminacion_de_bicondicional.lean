import analysis.special_functions.exp_log

open real

variables a b c d e : ℝ

#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (le_refl : ∀ (a : real), a ≤ a)

example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e :=
begin
  apply add_lt_add_of_lt_of_le,
  { apply add_lt_add_of_le_of_lt h₀,
    apply exp_lt_exp.mpr h₁ },
  apply le_refl
end

-- Nota: Con mpr se indica en modus pones inverso. Por ejemplo, si
-- h: A ↔ B, entonces h.mpr es B → A y h.mp es A → B

 
