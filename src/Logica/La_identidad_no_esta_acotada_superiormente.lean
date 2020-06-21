import data.real.basic

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

variable f : ℝ → ℝ

lemma aux (h : ∀ a, ∃ x, f x > a) : ¬ fn_has_ub f :=
begin
  intros fnub,
  cases fnub with a fnuba,
  cases h a with x hx,
  have : f x ≤ a,
    from fnuba x,
  linarith
end

example : ¬ fn_has_ub (λ x, x) :=
begin
  apply aux,
  intro a,
  use a + 1,
  linarith
end
