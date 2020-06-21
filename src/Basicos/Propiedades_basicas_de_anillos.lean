import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]

theorem add_zero (a : R) : a + 0 = a :=
by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 :=
by rw [add_comm, add_left_neg]

end my_ring

#check @my_ring.add_zero
-- | my_ring.add_zero : ∀ {R : Type u_1} [_inst_1 : ring R] (a : R), a + 0 = a

#check @add_zero
-- | add_zero : ∀ {M : Type u_1} [_inst_1 : add_monoid M] (a : M), a + 0 = a

-- Notas:
-- + Nota 1. Se usa {R : Type*} para declarar R como un argumento implícito.
-- + Nota 2: Se usa namespace para no evitar conflicto con nombres de mathlib
