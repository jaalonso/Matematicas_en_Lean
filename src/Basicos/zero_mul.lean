-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que en los anillos,
--    0 * a = 0
-- ----------------------------------------------------------------------

import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]

variable (a : R)

-- 1ª demostración
-- ===============

example : 0 * a = 0 :=
begin
  have h : 0 * a + 0 * a = 0 * a + 0,
    calc 0 * a + 0 * a
         = (0 + 0) * a : (add_mul 0 0 a).symm
     ... = 0 * a       : congr_arg (λ x, x * a) (add_zero 0)
     ... = 0 * a + 0   : self_eq_add_right.mpr rfl,
  rw add_left_cancel h
end

-- 2ª demostración
-- ===============

example : 0 * a = 0 :=
begin
  have h : 0 * a + 0 * a = 0 * a + 0,
    calc 0 * a + 0 * a
         = (0 + 0) * a : by rw add_mul
     ... = 0 * a       : by rw add_zero
     ... = 0 * a + 0   : by rw add_zero,
  rw add_left_cancel h
end

-- 3ª demostración
-- ===============

example : 0 * a = 0 :=
begin
  have h : 0 * a + 0 * a = 0 * a + 0,
  { rw [←add_mul, add_zero, add_zero] },
  rw add_left_cancel h
end

-- 4ª demostración
-- ===============

example : 0 * a = 0 :=
begin
  have h : 0 * a + 0 * a = 0 * a + 0,
    calc 0 * a + 0 * a
         = (0 + 0) * a : by simp
     ... = 0 * a       : by simp
     ... = 0 * a + 0   : by simp,
  simp,
end

end my_ring
