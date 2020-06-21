import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]

theorem sub_eq_add_neg (a b : R) : a - b = a + -b :=
rfl

example (a b : R) : a - b = a + -b :=
by reflexivity

end my_ring
