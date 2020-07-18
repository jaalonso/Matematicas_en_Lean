import data.nat.basic

example (a b : ℕ) (h : a ≠ b) : b ≠ a :=
begin
  symmetry, 
  exact h,
end
