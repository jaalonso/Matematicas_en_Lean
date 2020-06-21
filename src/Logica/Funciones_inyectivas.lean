import data.real.basic

open function

example (c : ℝ) : injective (λ x, x + c) :=
begin
  intros x₁ x₂ h',
  change x₁ + c = x₂ + c at h',
  apply add_right_cancel h'
end

example {c : ℝ} (h : c ≠ 0) : injective (λ x, c * x) :=
begin
  intros x₁ x₂ h',
  change c * x₁ = c * x₂ at h',
  apply mul_left_cancel' h h'
end

-- Lemas usados
-- ============

#check add_right_cancel a b c -- | a + b = b + c → b = c
#check mul_left_cancel' -- | c ≠ 0 → ∀ {y z : ℝ}, c * y = c * z → y = z
