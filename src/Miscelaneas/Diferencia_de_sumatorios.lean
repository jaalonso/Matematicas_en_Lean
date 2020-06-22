import tactic

open_locale big_operators

open finset

variables {R : Type*} [comm_ring R]

example 
  (f : ℕ → R) 
  (n m : ℕ) 
  (h : m ≤ n) :
  ∑ k in range n, f k - ∑ k in range m, f k = ∑ k in range (n - m), f (m + k) :=
begin
  rw ← sum_range_add_sum_Ico f h,
  simp only [add_sub_cancel'],
  rw sum_Ico_eq_sum_range,
end
