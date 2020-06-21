import data.real.basic

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

variable f : ℝ → ℝ

example (h : ∀ a, ∃ x, f x < a) : ¬ fn_has_lb f :=
begin
  intros fnlb,
  cases fnlb with a fnlba,
  cases h a with x hx,
  have : a ≤ f x,
    from fnlba x,
  linarith
end

