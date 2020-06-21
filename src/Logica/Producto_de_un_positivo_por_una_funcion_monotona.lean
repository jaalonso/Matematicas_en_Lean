import data.real.basic

variables (f g : ℝ → ℝ)

-- 1ª demostración
example {c : ℝ} (mf : monotone f) (nnc : 0 ≤ c) :
  monotone (λ x, c * f x) :=
begin 
    intros a b aleb,
    apply mul_le_mul_of_nonneg_left,
    apply mf aleb,
    apply nnc
end

-- 2ª demostración
example {c : ℝ} (mf : monotone f) (nnc : 0 ≤ c) :
  monotone (λ x, c * f x) :=
λ a b aleb, mul_le_mul_of_nonneg_left (mf aleb) nnc

