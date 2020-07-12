-- ---------------------------------------------------------------------
-- Ejercicio. Sea f una función de ℝ en ℝ. Demostrar que si f no tiene
-- cota superior, entonces para cada a existe un x tal que f(x) > a.
-- ----------------------------------------------------------------------

import data.real.basic

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

open_locale classical

variable (f : ℝ → ℝ)

-- 1ª demostración
-- ===============

example 
  (h : ¬ fn_has_ub f) 
  : ∀ a, ∃ x, f x > a :=
begin
  intro a,
  by_contradiction h1,
  apply h,
  use a,
  intro x,
  apply le_of_not_gt,
  intro h2,
  apply h1,
  use x,
  exact h2,
end

-- Prueba
-- ======

/-
f : ℝ → ℝ,
h : ¬fn_has_ub f
⊢ ∀ (a : ℝ), ∃ (x : ℝ), f x > a
  >> intro a,
a : ℝ
⊢ ∃ (x : ℝ), f x > a
  >> by_contradiction h1,
h1 : ¬∃ (x : ℝ), f x > a
⊢ false
  >> apply h,
⊢ fn_has_ub f
  >> use a,
⊢ fn_ub f a
  >> intro x,
x : ℝ
⊢ f x ≤ a
  >> apply le_of_not_gt,
⊢ ¬f x > a
  >> intro h2,
h2 : f x > a
⊢ false
  >> apply h1,
⊢ ∃ (x : ℝ), f x > a
  >> use x,
⊢ f x > a
  >> exact h2,
no goals
-/

-- 2ª demostración
example 
  (h : ¬ fn_has_ub f) : 
  ∀ a, ∃ x, f x > a :=
begin
  contrapose! h,
  exact h,
end

-- Prueba
-- ======

/-
f : ℝ → ℝ,
h : ¬fn_has_ub f
⊢ ∀ (a : ℝ), ∃ (x : ℝ), f x > a
  >> contrapose! h,
h : ∃ (a : ℝ), ∀ (x : ℝ), f x ≤ a
⊢ fn_has_ub f
  >> exact h,
no goals
-/

-- Comentario: La táctica (contrapose! h) aplica el contrapositivo entre
-- la hipótesis h y el objetivo; es decir, si (h : P) y el objetivo es Q
-- entonces cambia la hipótesis a (h : ¬Q) el objetivo a ¬P aplicando
-- simplificaciones en ambos. 
