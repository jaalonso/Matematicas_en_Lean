-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si a, b, c y d son números reales, entonces
--    (a + b) * (c + d) = a * c + a * d + b * c + b * d
-- ---------------------------------------------------------------------

import data.real.basic

variables a b c d : ℝ

-- 1ª demostración
-- ===============

example
  : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
calc
  (a + b) * (c + d)
      = a * (c + d) + b * (c + d)       : by rw add_mul
  ... = a * c + a * d + b * (c + d)     : by rw mul_add
  ... = a * c + a * d + (b * c + b * d) : by rw mul_add
  ... = a * c + a * d + b * c + b * d   : by rw ←add_assoc

-- 2ª demostración
-- ===============

example
  : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
calc
  (a + b) * (c + d)
      = a * (c + d) + b * (c + d)       : by ring
  ... = a * c + a * d + b * (c + d)     : by ring
  ... = a * c + a * d + (b * c + b * d) : by ring
  ... = a * c + a * d + b * c + b * d   : by ring

-- 3ª demostración
-- ===============

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
by ring

-- 4ª demostración
-- ===============

example
  : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
begin
   rw add_mul,
   rw mul_add,
   rw mul_add,
   rw ← add_assoc,
end

-- El desarrollo de la prueba es
--
--    a b c d : ℝ
--    ⊢ (a + b) * (c + d) = a * c + a * d + b * c + b * d
-- rw add_mul,
--    ⊢ a * (c + d) + b * (c + d) = a * c + a * d + b * c + b * d
-- rw mul_add,
--    ⊢ a * c + a * d + b * (c + d) = a * c + a * d + b * c + b * d
-- rw mul_add,
--    ⊢ a * c + a * d + (b * c + b * d) = a * c + a * d + b * c + b * d
-- rw ← add_assoc,
--    no goals

-- 5ª demostración
-- ===============

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
by rw [add_mul, mul_add, mul_add, ←add_assoc]
