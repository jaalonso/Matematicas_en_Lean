-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f no es monótona, entoces existen x, y
-- tales que x ≤ y y f(y) < f(x). 
-- ----------------------------------------------------------------------

import .Definicion_de_funciones_acotadas

open_locale classical

variable (f : ℝ → ℝ)

example 
  (h : ¬ monotone f) 
  : ∃ x y, x ≤ y ∧ f y < f x :=
begin
  simp only [monotone] at h,
  push_neg at h,
  exact h,
end

-- Prueba
-- ======

/-
f : ℝ → ℝ,
h : ¬monotone f
⊢ ∃ (x y : ℝ), x ≤ y ∧ f y < f x
  >> simp only [monotone] at h,
h : ¬∀ ⦃a b : ℝ⦄, a ≤ b → f a ≤ f b
⊢ ∃ (x y : ℝ), x ≤ y ∧ f y < f x
  >> push_neg at h,
h : ∃ ⦃a b : ℝ⦄, a ≤ b ∧ f b < f a
⊢ ∃ (x y : ℝ), x ≤ y ∧ f y < f x
  >> exact h,
no goals
-/
