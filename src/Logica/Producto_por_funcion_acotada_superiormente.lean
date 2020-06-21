import data.real.basic

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

variables {f g : ℝ → ℝ}

lemma fn_ub_mul {f : ℝ → ℝ} {a c : ℝ}
  (hfa : fn_ub f a) 
  (h : c ≥ 0) :
  fn_ub (λ x, c * f x) (c * a) :=
λ x, mul_le_mul_of_nonneg_left (hfa x) h

example {c : ℝ} (ubf : fn_has_ub f) (h : c ≥ 0):
  fn_has_ub (λ x, c * f x) :=
begin
  cases ubf with a ubfa,
  use c * a,
  apply fn_ub_mul ubfa h
end
