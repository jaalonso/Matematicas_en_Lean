-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    abs a = abs (a - b + b)
-- ----------------------------------------------------------------------

import data.real.basic

-- 1ª demostración
-- ===============

example 
  (a b : ℝ) 
  : abs a = abs (a - b + b) :=
begin 
  congr, 
  ring,
end

-- Prueba
-- ======

/-
a b : ℝ
⊢ abs a = abs (a - b + b)
  >> congr, 
⊢ a = a - b + b
  >> ring,
no goals
-/

-- Comentario: La táctica cong sustituye una conclusión de la forma 
-- A = B por las igualdades de sus subtérminos que no no iguales por
-- definición. Por ejemplo, sustituye la conclusión (x * f y = g w * f z)  
-- por las conclusiones (x = g w) y (y = z).

-- 2ª demostración
-- ===============

example 
  (a b : ℝ) 
  : abs a = abs (a - b + b) :=
by { congr, ring }

-- 3ª demostración
-- ===============

example 
  (a b : ℝ) 
  : abs a = abs (a - b + b) :=
by ring
