import tactic

example
  (m : ℕ)
  (h : m ∣ 4)
  : m = 1 ∨ m = 2 ∨ m = 4 :=
begin
  have := nat.le_of_dvd dec_trivial h,
  revert h,
  revert this,
  revert m,
  exact dec_trivial,
end
