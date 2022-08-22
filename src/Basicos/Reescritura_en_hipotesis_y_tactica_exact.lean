-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si a, b, c y d son números reales tales que
--    c = d * a + b
--    b = a * d
-- entonces
--    c = 2 * a * d
-- ---------------------------------------------------------------------

import data.real.basic

variables a b c d : ℝ

-- 1ª demostración
-- ===============

example
  (h1 : c = d * a + b)
  (h2 : b = a * d)
  : c = 2 * a * d :=
begin
  rw h2 at h1,
  clear h2,
  rw mul_comm d a at h1,
  rw ← two_mul (a*d) at h1,
  rewrite ← mul_assoc 2 a d at h1,
  exact h1,
end

-- Comentarios
-- 1. La táctica (rw e at h) rescribe la parte izquierda de la
--    ecuación e por la derecha en la hipótesis h.
-- 2. La táctica (exact p) tiene éxito si el tipo de p se unifica con el
--    objetivo.
-- 3. La táctica (clear h) borra la hipótesis h.

-- El desarrollo de la prueba es
--
--    a b c d : ℝ,
--    h1 : c = d * a + b,
--    h2 : b = a * d
--    ⊢ c = 2 * a * d
-- rw h2 at h1,
--    a b c d : ℝ,
--    h2 : b = a * d,
--    h1 : c = d * a + a * d
--    ⊢ c = 2 * a * d
-- clear h2,
--    a b c d : ℝ,
--    h1 : c = d * a + a * d
--    ⊢ c = 2 * a * d
-- rw mul_comm d a at h1,
--    a b c d : ℝ,
--    h1 : c = a * d + a * d
--    ⊢ c = 2 * a * d
-- rw ← two_mul (a*d) at h1,
--    a b c d : ℝ,
--    h1 : c = 2 * (a * d)
--    ⊢ c = 2 * a * d
-- rewrite ← mul_assoc 2 a d at h1,
--    a b c d : ℝ,
--    h1 : c = 2 * a * d
--    ⊢ c = 2 * a * d
-- exact h1
--    no goals

-- 2ª demostración
-- ===============

example
  (h1 : c = d * a + b)
  (h2 : b = a * d)
  : c = 2 * a * d :=
calc
  c = d * a + b       : by rw h1
  ... = d * a + a * d : by rw h2
  ... = a * d + a * d : by rw mul_comm d a
  ... = 2 * (a * d)   : by rw ← two_mul (a * d)
  ... = 2 * a * d     : by rw mul_assoc

-- 3ª demostración
-- ===============

example
  (h1 : c = d * a + b)
  (h2 : b = a * d)
  : c = 2 * a * d :=
by rw [h1, h2, mul_comm d a, ← two_mul (a * d), mul_assoc]

-- 4ª demostración
-- ===============

example
  (h1 : c = d * a + b)
  (h2 : b = a * d)
  : c = 2 * a * d :=
begin
  rw h1,
  rw h2,
  ring,
end

-- El desarrollo de la prueba es
--
--    a b c d : ℝ,
--    h1 : c = d * a + b,
--    h2 : b = a * d
--    ⊢ c = 2 * a * d
-- rw h1,
--    ⊢ d * a + b = 2 * a * d
-- rw h2,
--    ⊢ d * a + a * d = 2 * a * d
-- ring,
--    no goals

-- 5ª demostración
-- ===============

example
  (h1 : c = d * a + b)
  (h2 : b = a * d)
  : c = 2 * a * d :=
begin
  rw [h1, h2],
  ring,
end

-- 6ª demostración
-- ===============

example
  (h1 : c = d * a + b)
  (h2 : b = a * d)
  : c = 2 * a * d :=
by rw [h1, h2]; ring

-- 7ª demostración
-- ===============

example
  (h1 : c = d * a + b)
  (h2 : b = a * d)
  : c = 2 * a * d :=
by finish * using [two_mul]
