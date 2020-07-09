-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la teoría Definicion_de_funciones_acotadas
-- 2. Declarar f y g como variables de funciones de ℝ en ℝ. 
-- 3. Declarar a y b como variables sobre ℝ.
-- ----------------------------------------------------------------------

import .Definicion_de_funciones_acotadas -- 1

variables {f g : ℝ → ℝ}                  -- 2
variables {a b : ℝ}                      -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si a es una cota inferior de f y b lo es
-- de g, entonces a + b lo es de f + g.
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

lemma fn_lb_add 
  (hfa : fn_lb f a) 
  (hgb : fn_lb g b) 
  : fn_lb (λ x, f x + g x) (a + b) :=
begin
  intro x,
  change a + b ≤ f x + g x,
  apply add_le_add,
  apply hfa,
  apply hgb
end

-- Su desarrollo es
-- 
-- f g : ℝ → ℝ,
-- a b : ℝ,
-- hfa : fn_lb f a,
-- hgb : fn_lb g b
-- ⊢ fn_lb (λ (x : ℝ), f x + g x) (a + b)
--    >> intro x,
-- x : ℝ
-- ⊢ a + b ≤ (λ (x : ℝ), f x + g x) x
--    >> change a + b ≤ f x + g x,
-- ⊢ a + b ≤ f x + g x
--    >> apply add_le_add,
-- | ⊢ a ≤ f x
-- |    >> apply hfa,
-- | ⊢ b ≤ g x
-- |    >> apply hgb
-- no goals

-- 2ª demostración
-- ===============

example
  (hfa : fn_lb f a) 
  (hgb : fn_lb g b) 
  : fn_lb (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que la suma de dos funciones acotadas
-- inferiormente también lo está.
-- ----------------------------------------------------------------------

example 
  (lbf : fn_has_lb f) 
  (lbg : fn_has_lb g) 
  : fn_has_lb (λ x, f x + g x) :=
begin
  cases lbf with a lbfa,
  cases lbg with b lbgb,
  use a + b,
  apply fn_lb_add lbfa lbgb,
end

-- Su desarrollo es
-- 
-- f g : ℝ → ℝ,
-- lbf : fn_has_lb f,
-- lbg : fn_has_lb g
-- ⊢ fn_has_lb (λ (x : ℝ), f x + g x)
--    >> cases lbf with a lbfa,
-- f g : ℝ → ℝ,
-- lbg : fn_has_lb g,
-- a : ℝ,
-- lbfa : fn_lb f a
-- ⊢ fn_has_lb (λ (x : ℝ), f x + g x)
--    >> cases lbg with b lbgb,
-- f g : ℝ → ℝ,
-- a : ℝ,
-- lbfa : fn_lb f a,
-- b : ℝ,
-- lbgb : fn_lb g b
-- ⊢ fn_has_lb (λ (x : ℝ), f x + g x)
--    >> use a + b,
-- ⊢ fn_lb (λ (x : ℝ), f x + g x) (a + b)
--    >> apply fn_lb_add lbfa lbgb
-- no goals
