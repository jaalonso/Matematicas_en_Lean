import tactic

open_locale big_operators

variable (α : Type)

lemma sum_mul_sq_le_sq_mul_sq (s : finset α) (f g : α → ℝ) :
  (∑ i in s, f i * g i)^2 ≤ (∑ i in s, (f i)^2) * (∑ i in s, (g i)^2) :=
begin
  have : 0 ≤ ∑ i in s, (g i)^2 := sum_nonneg (λ i hi, sq_nonneg _),
  cases eq_or_lt_of_le this with h h,
  { rw [eq_comm, sum_eq_zero_iff_of_nonneg] at h,
    { simp only [nat.succ_pos', pow_eq_zero_iff] at h,
      rw [finset.sum_congr rfl (show ∀ i ∈ s, f i * g i = 0, from λ i hi, by simp [h i hi]),
          finset.sum_congr rfl (show ∀ i ∈ s, g i ^ 2 = 0, from λ i hi, by simp [h i hi])],
      simp },
    { intros i hi,
      apply sq_nonneg } },
  let lambda := (∑ i in s, f i * g i) / (∑ i in s, (g i)^2),
  have : 0 ≤ ∑ i in s, (f i - lambda * g i)^2,
  { apply sum_nonneg,
    intros i hi,
    apply sq_nonneg },
  simp_rw [sub_sq, sum_add_distrib, sum_sub_distrib, mul_pow, mul_assoc, ←mul_sum,
    mul_left_comm _ lambda, ←mul_sum, div_pow, div_mul_eq_mul_div, ←sq, ←div_mul_eq_mul_div,
    div_mul_eq_mul_div_comm, sq (∑ i in s, g i ^ 2), div_self_mul_self', ←div_eq_mul_inv, two_mul,
    ←sub_sub, sub_add_cancel, sub_nonneg] at this,
  rw div_le_iff h at this,
  assumption
end
