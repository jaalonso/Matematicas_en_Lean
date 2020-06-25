import data.real.basic

variables {x y : ℝ}

example : x < abs y → x < y ∨ x < -y :=
begin
  cases le_or_gt 0 y with h1 h2,
  { rw abs_of_nonneg h1,
    intro h3, 
    left, 
    exact h3 },
  { rw abs_of_neg h2,
    intro h4, 
    right, 
    exact h4 }
end
