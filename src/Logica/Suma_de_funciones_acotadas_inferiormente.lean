import data.real.basic

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

variables {f g : ℝ → ℝ}

lemma fn_lb_add (hfa : fn_lb f a) (hgb : fn_lb g b) :
  fn_lb (λ x, f x + g x) (a + b) :=
begin
  intro x,
  change a + b ≤ f x + g x,
  apply add_le_add,
  apply hfa,
  apply hgb
end

example (lbf : fn_has_lb f) (lbg : fn_has_lb g) :
  fn_has_lb (λ x, f x + g x) :=
begin
  cases lbf with a lbfa,
  cases lbg with b lbgb,
  use a + b,
  apply fn_lb_add lbfa lbgb
end

