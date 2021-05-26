import data.real.basic

example
  (a b : ℝ)
  (h : 1 = a ^ 2 + b ^ 2)
  : (1 - a) ^ 2 * 4 * 2 = (2 ^ 2 * b ^ 2 + 4 * (1 - a) ^ 2) * (1 - a) :=
by nlinarith
