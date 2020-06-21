import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]

theorem self_sub (a : R) : a - a = 0 :=
calc
  a - a = a + -a : by reflexivity
  ...   = 0      : by rw add_right_neg

end my_ring
