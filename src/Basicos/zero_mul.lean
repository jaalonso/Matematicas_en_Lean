import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]

theorem zero_mul (a : R) : 0 * a = 0 :=
have 0 * a + 0 = 0 * a + 0 * a, from calc
  0 * a + 0 = (0 + 0) * a   : by simp
        ... = 0 * a + 0 * a : by rw add_mul,
show 0 * a = 0, from (add_left_cancel this).symm

end my_ring
