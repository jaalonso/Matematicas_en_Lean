import data.real.basic
import tactic

example
  (a b : ℝ)
  (h : a * 2 = b + 1)
  : a + a = b - (-1) :=
begin
  convert h,
  { ring },
  { ring }
end

example
  (a b : ℝ)
  (h : a * 2 = b + 1)
  : a + a = 1 + b :=
begin
  convert h using 1, -- si se cambia a 2 no funciona
  { ring },
  { ring }
end

example
  (f : ℕ → ℕ)
  (a b : ℕ)
  (h : b = a)
  (h2 : f 2 = a)
  : f 2 = b :=
begin
  convert h2,
end
