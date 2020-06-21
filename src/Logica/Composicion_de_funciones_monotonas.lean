import data.real.basic

variables (f g : ℝ → ℝ)

-- 1ª demostración
example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f (g x)) :=
begin
  intros a b aleb,
  apply mf,
  apply mg,
  apply aleb
end

-- 2ª demostración
example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f (g x)) :=
λ a b aleb, mf (mg aleb)
