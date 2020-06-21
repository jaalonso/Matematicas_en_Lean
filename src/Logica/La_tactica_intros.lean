import data.real.basic

lemma my_lemma : ∀ {x y ε : ℝ},
  0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
begin
  intros x y ε epos ele1 xlt ylt,
  calc
    abs (x * y) = abs x * abs y : by rw abs_mul
            ... ≤ abs x * ε     : by rw [mul_le_mul_left' ylt]
            ... < ε * ε         : sorry
            ... ≤ 1 * ε         : sorry
            ... = ε             : by rw [one_mul]
end

-- Lemas usados
-- ============

#check (abs_mul : ∀ (a b : ℝ), abs (a * b) = abs a * abs b)
#check (mul_le_mul : a ≤ c → b ≤ d → 0 ≤ b → 0 ≤ c → a * b ≤ c * d)
#check (abs_nonneg : ∀ (a : ℝ), 0 ≤ abs a)
#check (mul_lt_mul_right : 0 < c → (a * c < b * c ↔ a < b))
#check (one_mul : ∀ (a : ℝ), 1 * a = a)
