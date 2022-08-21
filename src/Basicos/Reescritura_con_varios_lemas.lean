-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si a, b, c, d, e y f son números reales
-- tales que
--    a * b = c * d
--    e = f
-- entonces
--    a * (b * e) = c * (d * f)
-- ---------------------------------------------------------------------

import data.real.basic

-- 1ª demostración
-- ===============

example
  (a b c d e f : ℝ)
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
begin
  rw h2,
  rw ←mul_assoc,
  rw h1,
  rw mul_assoc,
end

-- Desarrollo de la prueba
--
--    a b c d e f : ℝ,
--    h1 : a * b = c * d,
--    h2 : e = f
--    ⊢ a * (b * e) = c * (d * f)
-- rw h2,
--    ⊢ a * (b * f) = c * (d * f)
-- rw ←mul_assoc,
--    ⊢ (a * b) * f = c * (d * f)
-- rw h1,
--    ⊢ (c * d) * f = c * (d * f)
-- rw mul_assoc,
--    no goals

-- 2ª demostración
-- ===============

example
  (a b c d e f : ℝ)
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
begin
  rw [h2, ←mul_assoc, h1, mul_assoc]
end

-- Comentario: Colocando el cursor en las comas se observa el progreso
-- en la ventana de objetivos.

-- 3ª demostración
-- ===============

example
  (a b c d e f : ℝ)
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
by rw [h2, ←mul_assoc, h1, mul_assoc]

-- 4ª demostración
-- ===============

example
  (a b c d e f : ℝ)
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
by finish

-- 5ª demostración
-- ===============

example
  (a b c d e f : ℝ)
  (h1 : a * b = c * d)
  (h2 : e = f)
  : a * (b * e) = c * (d * f) :=
calc
  a * (b * e) = a * (b * f) : by rw h2
          ... = (a * b) * f : by rw ←mul_assoc
          ... = (c * d) * f : by rw h1
          ... = c * (d * f) : by rw mul_assoc
