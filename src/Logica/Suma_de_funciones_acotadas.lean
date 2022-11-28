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
-- Ejercicio 2. Demostrar que si a es una cota superior de f y b lo es
-- de g, entonces a + b lo es de f + g.
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (hfa : fn_ub f a)
  (hgb : fn_ub g b)
  : fn_ub (f + g) (a + b) :=
begin
  assume x : ℝ,
  have h1 : f x ≤ a := hfa x,
  have h2 : g x ≤ b := hgb x,
  calc (f + g) x
       = f x + g x : rfl
   ... ≤ a + b     : add_le_add h1 h2
end

-- 2ª demostración
-- ===============

example
  (hfa : fn_ub f a)
  (hgb : fn_ub g b)
  : fn_ub (f + g) (a + b) :=
begin
  intro x,
  change f x + g x ≤ a + b,
  apply add_le_add,
  apply hfa,
  apply hgb
end

-- Su desarrollo es
--
-- f g : ℝ → ℝ,
-- a b : ℝ,
-- hfa : fn_ub f a,
-- hgb : fn_ub g b
-- ⊢ fn_ub (λ (x : ℝ), f x + g x) (a + b)
--    >> intro x,
-- x : ℝ
-- ⊢ (λ (x : ℝ), f x + g x) x ≤ a + b
--    >> change f x + g x ≤ a + b,
-- ⊢ f x + g x ≤ a + b
--    >> apply add_le_add,
-- | ⊢ f x ≤ a
-- |    >> apply hfa,
-- | ⊢ g x ≤ b
-- |    >> apply hgb
-- no goals

-- 3ª demostración
-- ===============

theorem fn_ub_add
  (hfa : fn_ub f a)
  (hgb : fn_ub g b)
  : fn_ub (f + g) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que la suma de dos funciones acotadas
-- superiormente también lo está.
-- ----------------------------------------------------------------------

lemma aux
  (ubf : fn_has_ub f)
  (ubg : fn_has_ub g) :
  fn_has_ub (λ x, f x + g x) :=
begin
  cases ubf with a ubfa,
  cases ubg with b ubfb,
  use a + b,
  apply fn_ub_add ubfa ubfb,
end

-- Su desarrollo es
--
-- f g : ℝ → ℝ,
-- ubf : fn_has_ub f,
-- ubg : fn_has_ub g
-- ⊢ fn_has_ub (λ (x : ℝ), f x + g x)
--    >> cases ubf with a ubfa,
-- f g : ℝ → ℝ,
-- ubg : fn_has_ub g,
-- a : ℝ,
-- ubfa : fn_ub f a
-- ⊢ fn_has_ub (λ (x : ℝ), f x + g x)
--    >> cases ubg with b ubfb,
-- f g : ℝ → ℝ,
-- a : ℝ,
-- ubfa : fn_ub f a,
-- b : ℝ,
-- ubfb : fn_ub g b
-- ⊢ fn_has_ub (λ (x : ℝ), f x + g x)
--    >> use a + b,
-- ⊢ fn_ub (λ (x : ℝ), f x + g x) (a + b)
--    >> apply fn_ub_add ubfa ubfb
-- no goals
