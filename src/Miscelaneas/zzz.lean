import data.nat.basic
import data.rat.basic
import data.rat.order
import algebra.pi_instances
import tactic

def neg_fn (μ : ℕ → ℚ) : Prop :=
  ∀ (c : ℕ), ∃ (n₀ : ℕ),
    ∀ (n : ℕ), n₀ ≤ n → (μ n) * (n ^ c) < 1

theorem sum_neg_fn_is_neg_fn :
  ∀ (μ₁ μ₂ : ℕ → ℚ), neg_fn μ₁ → neg_fn μ₂ → neg_fn (μ₁ + μ₂) :=
begin
  intros μ₁ μ₂ H₁ H₂ c,
  cases H₁ (c + 2) with n₁ Hn₁,
  cases H₂ (c + 2) with n₂ Hn₂,
  use max n₁ (max n₂ 2), intros n Hn,
  repeat { rw max_le_iff at Hn },
  rcases Hn with ⟨Ht₁, Ht₂, Ht₃⟩,
  specialize Hn₁ n Ht₁,
  specialize Hn₂ n Ht₂,
  rw pi.add_apply,
  rw [pow_add, ←mul_assoc] at Hn₁ Hn₂,
  have npos : 0 < (↑n : ℚ), { norm_cast, linarith },
  have hsqp : 0 < (↑n : ℚ) ^ 2 := pow_pos npos 2,
  rw ←lt_div_iff hsqp at Hn₁ Hn₂,
  have Ht₃' : (4 : ℚ) ≤ (↑n : ℚ)^2,
  { norm_cast, exact nat.pow_le_pow_of_le_left Ht₃ 2 },
  have Ht₃'' : 1/(↑n : ℚ)^2 ≤ 1/(4 : ℚ),
  { exact div_le_div_of_le_left zero_le_one (by linarith) Ht₃' },
  linarith [Hn₁, Hn₂, Ht₃''],
end
