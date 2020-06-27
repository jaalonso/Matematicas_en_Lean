import data.real.basic

example 
  {z : ℝ}      
  (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1) :
  z ≥ 0 :=
begin
  rcases h with ⟨a, b, ⟨h1, h2⟩⟩,
  { apply add_nonneg,
    apply pow_two_nonneg,
    apply pow_two_nonneg },
  { rw h_h_h,
    apply add_nonneg,
    apply add_nonneg,
    apply pow_two_nonneg,
    apply pow_two_nonneg,
    exact zero_le_one },
end
 
