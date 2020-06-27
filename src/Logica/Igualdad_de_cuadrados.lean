import data.real.basic

variables (x y : ℝ)

example 
  (h : x^2 = 1) : 
  x = 1 ∨ x = -1 :=
begin
  have h1 : (x - 1) * (x + 1) = 0,
    calc (x - 1) * (x + 1) = x^2 - 1 : by ring
                       ... = 1 - 1   : by rw h
                       ... = 0       : by ring,
  have h2 : x - 1 = 0 ∨ x + 1 = 0, 
    { apply eq_zero_or_eq_zero_of_mul_eq_zero h1 },
  cases h2,
  { left,
    exact sub_eq_zero.mp h2 },
  { right,
    exact eq_neg_of_add_eq_zero h2 },
end

example 
  (h : x^2 = y^2) : 
  x = y ∨ x = -y :=
begin
  have h1 : (x - y) * (x + y) = 0,
    calc (x - y) * (x + y) = x^2 - y^2 : by ring
                       ... = y^2 - y^2 : by rw h
                       ... = 0         : by ring,
  have h2 : x - y = 0 ∨ x + y = 0, 
    { apply eq_zero_or_eq_zero_of_mul_eq_zero h1 },
  cases h2,
  { left,
    exact sub_eq_zero.mp h2 },
  { right,
    exact eq_neg_of_add_eq_zero h2 },
end


