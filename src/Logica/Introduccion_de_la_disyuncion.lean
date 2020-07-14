-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la librería de los números naturales.
-- 2. Declarar x e y como variables sobre los reales. 
-- ----------------------------------------------------------------------

import data.real.basic   -- 1
variables {x y : ℝ}      -- 2

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    y > x^2)
-- entonces
--    y > 0 ∨ y < -1 
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example 
  (h : y > x^2) 
  : y > 0 ∨ y < -1 :=
begin 
  left, 
  linarith [pow_two_nonneg x],
end

-- Prueba
-- ======

/-
x y : ℝ,
h : y > x ^ 2
⊢ y > 0 ∨ y < -1
  >> left, 
⊢ y > 0
  >> linarith [pow_two_nonneg x],
no goals
-/

-- Comentarios:
-- 1. La táctica left, si el objetivo es una disjunción (P ∨ Q), aplica
--    la regla de introducción de la disyunción; es decir, cambia el
--    objetivo por P. Ver https://bit.ly/3enkT3d
-- 2. Se usa el lema
--       pow_two_nonneg x : 0 ≤ x ^ 2     

-- 2ª demostración
-- ===============

example 
  (h : y > x^2) 
  : y > 0 ∨ y < -1 :=
by { left, linarith [pow_two_nonneg x] }

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si
--    -y > x^2 + 1 
-- entonces
--    y > 0 ∨ y < -1 
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example 
  (h : -y > x^2 + 1) 
  : y > 0 ∨ y < -1 :=
begin 
  right, 
  linarith [pow_two_nonneg x],
end

-- Prueba
-- ======

/-
x y : ℝ,
h : -y > x ^ 2 + 1
⊢ y > 0 ∨ y < -1
  >> right, 
⊢ y < -1
  >> linarith [pow_two_nonneg x],
no goals
-/

-- Comentarios:
-- 1. La táctica right, si el objetivo es una disjunción (P ∨ Q), aplica
--    la regla de introducción de la disyunción; es decir, cambia el
--    objetivo por Q. Ver https://bit.ly/3enkT3d
-- 2. Se usa el lema
--       pow_two_nonneg x : 0 ≤ x ^ 2     

-- 2ª demostración
-- ===============

example 
  (h : -y > x^2 + 1) 
  : y > 0 ∨ y < -1 :=
by { right, linarith [pow_two_nonneg x] }

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que si
--      y > 0
-- entonces
--      y > 0 ∨ y < -1 
-- ----------------------------------------------------------------------

example 
  (h : y > 0) 
  : y > 0 ∨ y < -1 :=
or.inl h

-- Comentario: Se usa el lema
--    or.inl : a → a ∨ b

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que si
--    y < -1
-- entonces
--    y > 0 ∨ y < -1
-- ----------------------------------------------------------------------

example 
  (h : y < -1) 
  : y > 0 ∨ y < -1 :=
or.inr h

-- Comentario: Se usa el lema
--    or.inr : b → a ∨ b

