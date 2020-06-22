import data.real.basic

theorem not_monotone_iff 
  {f : ℝ → ℝ}:
  ¬ monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
by { rw [monotone], push_neg }

example : ¬ monotone (λ x : ℝ, -x) :=
begin
  apply not_monotone_iff.mpr,
  use [2, 3],
  norm_num,
end
