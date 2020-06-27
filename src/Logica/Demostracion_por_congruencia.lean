import data.real.basic

example (a b : ℝ) : abs a = abs (a - b + b) :=
by { congr, ring }
