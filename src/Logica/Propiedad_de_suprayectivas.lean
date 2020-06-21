import data.real.basic

open function

example 
  {f : ℝ → ℝ} 
  (h : surjective f) : 
  ∃ x, (f x)^2 = 4 :=
begin
  cases h 2 with x hx,
  use x,
  rw hx,
  norm_num
end

