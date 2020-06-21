import data.real.basic

variables a b c d : ℝ

example (a b c d e : ℝ) 
  (h₀ : a ≤ b) 
  (h₁ : b < c) 
  (h₂ : c ≤ d)
  (h₃ : d < e) :
  a < e :=
by linarith

example 
  (h   : 2 * a ≤ 3 * b) 
  (h'  : 1 ≤ a) 
  (h'' : d = 2) :
  d + a ≤ 5 * b :=
by linarith
