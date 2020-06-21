import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c :=
calc
  b 
      = 0 + b        : by rw zero_add
  ... = (-a + a) + b : by rw add_left_neg
  ... = -a + (a + b) : by rw add_assoc
  ... = -a + (a + c) : by rw h
  ... = (-a + a) + c : by rw ←add_assoc
  ... = 0 + c        : by rw add_left_neg
  ... = c            : by rw zero_add

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c :=
calc 
  a 
      = a + 0        : by rw add_zero
  ... = a + (b + -b) : by rw add_right_neg
  ... = (a + b) + -b : by rw add_assoc
  ... = (c + b) + -b : by rw h
  ... = c + (b + -b) : by rw ← add_assoc
  ... = c + 0        : by rw ← add_right_neg
  ... = c            : by rw add_zero 

end my_ring
