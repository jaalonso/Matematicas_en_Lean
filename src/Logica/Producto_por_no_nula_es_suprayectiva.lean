import data.real.basic

open function

example {c : ℝ} 
  (h : c ≠ 0) : 
  surjective (λ x, c * x) :=
begin
  intro x,
  use (x / c),
  change c * (x / c) = x,
  rw mul_comm,
  apply div_mul_cancel,
  exact h
end
