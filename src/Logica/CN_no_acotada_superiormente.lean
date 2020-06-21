import data.real.basic

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

open_locale classical

variable (f : ℝ → ℝ)

example 
  (h : ¬ fn_has_ub f) : 
  ∀ a, ∃ x, f x > a :=
begin
  intro a,
  by_contradiction h1,
  apply h,
  use a,
  intro x,
  apply le_of_not_gt,
  intro h2,
  apply h1,
  use x,
  exact h2
end
