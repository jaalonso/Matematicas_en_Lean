-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si son números reales, entonces
--    (a + b) * (a + b) = a * a + 2 * (a * b) + b * b
-- ---------------------------------------------------------------------

import data.real.basic

variables a b : ℝ

-- 1ª demostración
-- ===============

example : 
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
begin
  rw mul_add,
  rw add_mul, 
  rw add_mul,
  rw ← add_assoc,
  rw add_assoc (a * a),
  rw mul_comm b a, 
  rw ← two_mul,
end

-- El desarrollo de la prueba es
--
--    a b : ℝ
--    ⊢ (a + b) * (a + b) = a * a + 2 * (a * b) + b * b
-- rw mul_add,
--    ⊢ (a + b) * a + (a + b) * b = a * a + 2 * (a * b) + b * b
-- rw add_mul, 
--    ⊢ a * a + b * a + (a + b) * b = a * a + 2 * (a * b) + b * b
-- rw add_mul,
--    ⊢ a * a + b * a + (a * b + b * b) = a * a + 2 * (a * b) + b * b
-- rw ← add_assoc,
--    ⊢ a * a + b * a + a * b + b * b = a * a + 2 * (a * b) + b * b
-- rw add_assoc (a * a),
--    ⊢ a * a + (b * a + a * b) + b * b = a * a + 2 * (a * b) + b * b
-- rw mul_comm b a, 
--    ⊢ a * a + (a * b + a * b) + b * b = a * a + 2 * (a * b) + b * b
-- rw ← two_mul,
--    no goals

-- 2ª demostración
-- ===============

example : 
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b) 
      = (a + b) * a + (a + b) * b       : by rw mul_add
  ... = a * a + b * a + (a + b) * b     : by rw add_mul 
  ... = a * a + b * a + (a * b + b * b) : by rw add_mul 
  ... = a * a + b * a + a * b + b * b   : by rw ← add_assoc
  ... = a * a + (b * a + a * b) + b * b : by rw add_assoc (a * a)
  ... = a * a + (a * b + a * b) + b * b : by rw mul_comm b a 
  ... = a * a + 2 * (a * b) + b * b   : by rw ← two_mul

-- 3ª demostración
-- ===============

example : 
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
begin
  rw [mul_add, add_mul, add_mul],
  rw [←add_assoc, add_assoc (a * a)],
  rw [mul_comm b a, ←two_mul],
end

-- El desarrollo de la prueba es
-- 
--    a b : ℝ
--    ⊢ a * a + (a * b + a * b) + b * b = a * a + 2 * (a * b) + b * b
-- rw [mul_add, add_mul, add_mul],
--    ⊢ a * a + b * a + (a * b + b * b) = a * a + 2 * (a * b) + b * b
-- rw [←add_assoc, add_assoc (a * a)],
--    ⊢ a * a + (b * a + a * b) + b * b = a * a + 2 * (a * b) + b * b
-- rw [mul_comm b a, ←two_mul]
--    no goals

-- 4ª demostración
-- ===============

example : 
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
calc
  (a + b) * (a + b)
      = a * a + b * a + (a * b + b * b) : by rw [mul_add, add_mul, add_mul]
  ... = a * a + (b * a + a * b) + b * b : by rw [←add_assoc, add_assoc (a * a)]
  ... = a * a + 2 * (a * b) + b * b     : by rw [mul_comm b a, ←two_mul]

-- 4ª demostración
-- ===============

example : 
  (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
by ring
