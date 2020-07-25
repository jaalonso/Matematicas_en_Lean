-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (λ x y : ℝ, (x + y)^2) = (λ x y : ℝ, x^2 + 2*x*y + y^2)
-- ----------------------------------------------------------------------

import data.real.basic

-- 1ª demostración
-- ===============

example : (λ x y : ℝ, (x + y)^2) = (λ x y : ℝ, x^2 + 2*x*y + y^2) :=
begin 
  ext, 
  ring,
end

-- Prueba
-- ======

/-
⊢ (λ (x y : ℝ), (x + y) ^ 2) = λ (x y : ℝ), x ^ 2 + 2 * x * y + y ^ 2
  >> ext,
⊢ (x + x_1) ^ 2 = x ^ 2 + 2 * x * x_1 + x_1 ^ 2 
  >> ring,
no goals
-/

-- Comentario: La táctica ext transforma las conclusiones de la forma
-- (λ x, f x) = (λ x, g x) en f x = g x. 


-- 2ª demostración
-- ===============

example : (λ x y : ℝ, (x + y)^2) = (λ x y : ℝ, x^2 + 2*x*y + y^2) :=
by { ext, ring }

-- 3ª demostración
-- ===============

example : (λ x y : ℝ, (x + y)^2) = (λ x y : ℝ, x^2 + 2*x*y + y^2) :=
by ring
