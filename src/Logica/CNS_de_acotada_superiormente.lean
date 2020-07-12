-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones:
-- 1. Importar la teoría Definicion_de_funciones_acotadas
-- 2. Habilitar la lógica clásica.
-- 3. Declarar f como una variable de ℝ en ℝ.
-- ----------------------------------------------------------------------

import .Definicion_de_funciones_acotadas   -- 1
open_locale classical                      -- 2
variable (f : ℝ → ℝ)                       -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    ¬ ∀ a, ∃ x, f x > a
-- entonces f está acotada superiormente.
-- ----------------------------------------------------------------------

example 
  (h : ¬ ∀ a, ∃ x, f x > a) 
  : fn_has_ub f :=
begin
  push_neg at h,
  exact h,
end

-- Prueba
-- ======

/-
f : ℝ → ℝ,
h : ¬∀ (a : ℝ), ∃ (x : ℝ), f x > a
⊢ fn_has_ub f
  >> push_neg at h,
h : ∃ (a : ℝ), ∀ (x : ℝ), f x ≤ a
⊢ fn_has_ub f
  >> exact h,
no goals
-/

-- Comentario. La táctica (push_neg at h) interioriza las negaciones de
-- la hipótesis h.

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si f no tiene cota superior, entonces para
-- cada a existe un x tal que f(x) > a.
-- ----------------------------------------------------------------------

example 
  (h : ¬ fn_has_ub f) 
  : ∀ a, ∃ x, f x > a :=
begin
  simp only [fn_has_ub, fn_ub] at h,
  push_neg at h,
  exact h,
end

-- Prueba
-- ======

/-
f : ℝ → ℝ,
h : ¬fn_has_ub f
⊢ ∀ (a : ℝ), ∃ (x : ℝ), f x > a
  >> simp only [fn_has_ub, fn_ub] at h,
h : ¬∃ (a : ℝ), ∀ (x : ℝ), f x ≤ a
⊢ ∀ (a : ℝ), ∃ (x : ℝ), f x > a
  >> push_neg at h,
h : ∀ (a : ℝ), ∃ (x : ℝ), a < f x
⊢ ∀ (a : ℝ), ∃ (x : ℝ), f x > a
  >> exact h,
no goals
-/

-- Comentario: La táctica (simp only [h₁, ..., hₙ] at h) simplifica la
-- hipótesis h usando sólo los lemas h₁, ..., hₙ. (Ver 
-- https://bit.ly/38O60EV)
