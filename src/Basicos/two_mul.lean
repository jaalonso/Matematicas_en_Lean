import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]

lemma one_add_one_eq_two : 1 + 1 = (2 : R) :=
by refl

theorem two_mul (a : R) : 2 * a = a + a :=
calc
  2 * a = (1 + 1) * a   : by refl
  ...   = 1 * a + 1 * a : by rw add_mul
  ...   = a + a         : by rw one_mul

end my_ring
