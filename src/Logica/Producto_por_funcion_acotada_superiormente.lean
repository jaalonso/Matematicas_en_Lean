-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la teoría Definicion_de_funciones_acotadas
-- 2. Declarar f como variable de funciones de ℝ en ℝ. 
-- 3. Declarar a y c como variables sobre ℝ.
-- ----------------------------------------------------------------------

import .Definicion_de_funciones_acotadas -- 1

variables {f : ℝ → ℝ}                    -- 2
variables {a c : ℝ}                      -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si a es una cota superior de f y c no es
-- negativo, entonces c * a es una cota superior de c * f.
-- ----------------------------------------------------------------------

lemma fn_ub_mul 
  (hfa : fn_ub f a) 
  (h : c ≥ 0) 
  : fn_ub (λ x, c * f x) (c * a) :=
λ x, mul_le_mul_of_nonneg_left (hfa x) h

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si c ≥ 0 y f está acotada superiormente,
-- entonces c * f también lo está.
-- ----------------------------------------------------------------------

example 
  (ubf : fn_has_ub f) 
  (h : c ≥ 0)
  : fn_has_ub (λ x, c * f x) :=
begin
  cases ubf with a ubfa,
  use c * a,
  apply fn_ub_mul ubfa h,
end

-- Su desarrollo es
-- 
-- f : ℝ → ℝ,
-- c : ℝ,
-- ubf : fn_has_ub f,
-- h : c ≥ 0
-- ⊢ fn_has_ub (λ (x : ℝ), c * f x)
--    >> cases ubf with a ubfa,
-- a : ℝ,
-- ubfa : fn_ub f a
-- ⊢ fn_has_ub (λ (x : ℝ), c * f x)
--    >> use c * a,
-- ⊢ fn_ub (λ (x : ℝ), c * f x) (c * a)
--    >> apply fn_ub_mul ubfa h
-- no goals
