import data.real.basic

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

open_locale classical

variable (f : ℝ → ℝ)

example 
  (h : ¬ monotone f) : 
  ∃ x y, x ≤ y ∧ f y < f x :=
begin
  simp only [monotone] at h,
  push_neg at h,
  exact h
end
