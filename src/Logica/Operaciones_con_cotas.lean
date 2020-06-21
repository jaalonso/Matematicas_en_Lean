import data.real.basic

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

variables (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : fn_lb f a) (hgb : fn_lb g b) :
  fn_lb (λ x, f x + g x) (a + b) :=
begin
  intro x,
  -- dsimp,
  change a + b ≤ f x + g x,
  apply add_le_add,
  apply hfa,
  apply hgb
end

example (nnf : fn_lb f 0) (nng : fn_lb g 0) :
  fn_lb (λ x, f x * g x) 0 :=
begin
  intro x,
  change 0 ≤ f x * g x,
  apply mul_nonneg,
  apply nnf,
  apply nng
end

example (hfa : fn_ub f a) (hfb : fn_ub g b)
    (nng : fn_lb g 0) (nna : 0 ≤ a) :
  fn_ub (λ x, f x * g x) (a * b) :=
begin
  intro x,
  change f x * g x ≤ a * b,
  apply mul_le_mul,
  apply hfa,
  apply hfb,
  apply nng,
  apply nna
end
