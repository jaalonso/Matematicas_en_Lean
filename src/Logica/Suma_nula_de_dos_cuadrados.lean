import data.real.basic

theorem aux 
  {x y : ℝ} 
  (h : x^2 + y^2 = 0) : 
  x = 0 :=
begin
  have h' : x^2 = 0,
    { apply le_antisymm,
      show x ^ 2 ≤ 0,
        calc
          x ^ 2 ≤ x^2 + y^2 : by simp [le_add_of_nonneg_right, pow_two_nonneg]
            ... = 0         : by exact h,
      apply pow_two_nonneg,
    },
  exact pow_eq_zero h'
end

example (x y : ℝ) : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 :=
begin
  split,
    intro h,
    split,
     apply (aux h),
    rw add_comm at h,
    apply (aux h),
  intro h1,
  cases h1 with h2 h3,
  rw [h2, h3],
  ring
end

-- Lemas usados
-- ============

#check (pow_two_nonneg : ∀ (a : ℝ), 0 ≤ a ^ 2)

variable x : ℝ
variable n : ℕ
#check (pow_eq_zero : x ^ n = 0 → x = 0)
