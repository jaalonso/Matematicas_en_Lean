import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b :=
by rw [←add_assoc, add_left_neg, zero_add]

end my_ring
