import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b :=
calc
  -a  = -a + 0       : by rw add_zero
  ... = -a + (a + b) : by rw h
  ... = b            : by rw neg_add_cancel_left

lemma neg_add_cancel_right {a b : R} : (a + b) + -b = a :=
by rw [add_assoc, add_right_neg, add_zero]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b :=
calc 
  a   = (a + b) + -b : by rw neg_add_cancel_right
  ... = 0 + -b       : by rw h
  ... = -b           : by rw zero_add

theorem neg_zero : (-0 : R) = 0 :=
begin
  apply neg_eq_of_add_eq_zero,
  rw add_zero,
end

theorem neg_neg (a : R) : -(-a) = a :=
begin
  apply neg_eq_of_add_eq_zero,
  rw add_left_neg,
end

end my_ring
