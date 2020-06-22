import data.real.basic

variables {x y : ℝ}

example 
  (h : y > x^2) : 
  y > 0 ∨ y < -1 :=
by { left, linarith [pow_two_nonneg x] }

example 
  (h : -y > x^2 + 1) : 
  y > 0 ∨ y < -1 :=
by { right, linarith [pow_two_nonneg x] }

variable {y : ℝ}

example (h : y > 0) : y > 0 ∨ y < -1 :=
or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
or.inr h
