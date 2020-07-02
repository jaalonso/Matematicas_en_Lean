-- ---------------------------------------------------------------------
-- Ejercicio 1. Demostrar que los números reales tienen la siguente
-- propiedad 
--    (c * b) * a = b * (a * c)
-- ---------------------------------------------------------------------

-- Importación de librería
-- =======================

import data.real.basic

-- 1ª demostración
-- ===============

example 
  (a b c : ℝ) 
  : (c * b) * a = b * (a * c) :=
begin
  rw mul_comm c b,
  rw mul_assoc,
  rw mul_comm c a,
end

-- Desarrollo de la prueba:
-- -----------------------

--    a b c : ℝ
--    ⊢ (c * b) * a = b * (a * c)
-- rw mul_comm c b,
--    a b c : ℝ
--    ⊢ (b * c) * a = b * (a * c)
-- rw mul_assoc,
--    a b c : ℝ
--    ⊢ b * (c * a) = b * (a * c)
-- rw mul_comm c a,
--   no goals

-- 2ª demostración
-- ===============

example 
  (a b c : ℝ) 
  : (c * b) * a = b * (a * c) :=
calc
  (c * b) * a = (b * c) * a : by rw mul_comm c b
          ... = b * (c * a) : by rw mul_assoc
          ... = b * (a * c) : by rw mul_comm c a

-- 3ª demostración
-- ===============

example 
  (a b c : ℝ) 
  : (c * b) * a = b * (a * c) :=
by ring

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que los números reales tienen la siguente
-- propiedad 
--    a * (b * c) = b * (a * c)
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example 
  (a b c : ℝ) 
  : a * (b * c) = b * (a * c) :=
begin
  rw ←mul_assoc,
  rw mul_comm a b,
  rw mul_assoc,
end

-- Comentario. Con la táctica (rw ←e) se aplica reescritura sustituyendo
-- el término derecho de la igualdad e por el izquierdo.

-- Desarrollo de la prueba
-- -----------------------

--    a b c : ℝ
--    ⊢ a * (b * c) = b * (a * c)
-- rw ←mul_assoc,
--    a b c : ℝ
--    ⊢ (a * b) * c = b * (a * c)
-- rw mul_comm a b,
--    a b c : ℝ
--    ⊢ (b * a) * c = b * (a * c)
-- rw mul_assoc,
--    no goals

-- 2ª demostración
-- ===============

example 
  (a b c : ℝ) 
  : a * (b * c) = b * (a * c) :=
calc
  a * (b * c) = (a * b) * c : by rw ←mul_assoc
          ... = (b * a) * c : by rw mul_comm a b
          ... = b * (a * c) : by rw mul_assoc

-- 3ª demostración
-- ===============

example 
  (a b c : ℝ) 
  : a * (b * c) = b * (a * c) :=
by ring
