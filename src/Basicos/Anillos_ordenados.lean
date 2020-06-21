import algebra.ordered_ring

variables {R : Type*} [ordered_ring R]
variables a b c : R

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)
#check (zero_ne_one : (0 : R) ≠ 1)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
