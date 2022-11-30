-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la teoría Definicion_de_funciones_acotadas
-- 2. Declarar f y g como variable de funciones de ℝ en ℝ.
-- 3. Declarar a y c como variables sobre ℝ.
-- ----------------------------------------------------------------------

import .Definicion_de_funciones_acotadas -- 1

variables {f g : ℝ → ℝ}                  -- 2
variables {a b : ℝ}                      -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si a es una cota superior de f y b es una
-- cota superior de g, entonces a + b lo es de f + g.
-- ----------------------------------------------------------------------

theorem fn_ub_add
  (hfa : fn_ub f a)
  (hgb : fn_ub g b)
  : fn_ub (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si f y g está acotadas superiormente,
-- entonces f + g también lo está.
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (ubf : fn_has_ub f)
  (ubg : fn_has_ub g)
  : fn_has_ub (λ x, f x + g x) :=
begin
  rcases ubf with ⟨a, ubfa⟩,
  rcases ubg with ⟨b, ubfb⟩,
  exact ⟨a + b, fn_ub_add ubfa ubfb⟩,
end

-- Su desarrollo es
--
-- f g : ℝ → ℝ,
-- ubf : fn_has_ub f,
-- ubg : fn_has_ub g
-- ⊢ fn_has_ub (λ (x : ℝ), f x + g x)
--    >> rcases ubf with ⟨a, ubfa⟩,
-- f g : ℝ → ℝ,
-- ubg : fn_has_ub g,
-- a : ℝ,
-- ubfa : fn_ub f a
-- ⊢ fn_has_ub (λ (x : ℝ), f x + g x)
--    >> rcases ubg with ⟨b, ubfb⟩,
-- f g : ℝ → ℝ,
-- a : ℝ,
-- ubfa : fn_ub f a,
-- b : ℝ,
-- ubfb : fn_ub g b
-- ⊢ fn_has_ub (λ (x : ℝ), f x + g x)
--    >> exact ⟨a + b, fn_ub_add ubfa ubfb⟩
-- no goals

-- 2ª demostración
-- ===============

example :
  fn_has_ub f →
  fn_has_ub g →
  fn_has_ub (λ x, f x + g x) :=
begin
  rintros ⟨a, ubfa⟩ ⟨b, ubfb⟩,
  exact ⟨a + b, fn_ub_add ubfa ubfb⟩,
end

-- Su desarrollo es
--
-- f g : ℝ → ℝ
-- ⊢ fn_has_ub f → fn_has_ub g → fn_has_ub (λ (x : ℝ), f x + g x)
--    >> rintros ⟨a, ubfa⟩ ⟨b, ubfb⟩,
-- f g : ℝ → ℝ,
-- a : ℝ,
-- ubfa : fn_ub f a,
-- b : ℝ,
-- ubfb : fn_ub g b
-- ⊢ fn_has_ub (λ (x : ℝ), f x + g x)
--    >> exact ⟨a + b, fn_ub_add ubfa ubfb⟩
-- no goals

-- 3ª demostración
-- ===============

example : fn_has_ub f → fn_has_ub g →
  fn_has_ub (λ x, f x + g x) :=
λ ⟨a, ubfa⟩ ⟨b, ubfb⟩, ⟨a + b, fn_ub_add ubfa ubfb⟩
