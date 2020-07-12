-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la teoría de los números reales.
-- 2. Declarar f como una variable sobre las funciones de ℝ en ℝ.  
-- ----------------------------------------------------------------------

import data.real.basic   -- 1
variable {f : ℝ → ℝ}     -- 2

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que f es no monótona syss existen x e y tales
-- que x ≤ y y f(x) > f(y).
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ================

example :
  ¬ monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
begin 
  rw [monotone], 
  push_neg,
end

-- Prueba
-- ======

/-
f : ℝ → ℝ
⊢ ¬monotone f ↔ ∃ (x y : ℝ), x ≤ y ∧ f x > f y
  >> rw [monotone], 
⊢ (¬∀ ⦃a b : ℝ⦄, a ≤ b → f a ≤ f b) ↔ ∃ (x y : ℝ), x ≤ y ∧ f x > f y
  >> push_neg,
no goals
-/

-- Comentario: Se ha usado la definición
-- + monotone: ∀ ⦃a b : ℝ⦄, a ≤ b → f a ≤ f b

-- 2ª demostración
-- ================

lemma not_monotone_iff :
  ¬ monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
by { rw [monotone], push_neg }

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que la función opuesta no es monótona.
-- ----------------------------------------------------------------------

example : ¬ monotone (λ x : ℝ, -x) :=
begin
  apply not_monotone_iff.mpr,
  use [2, 3],
  norm_num,
end

-- Prueba
-- ======

/-
⊢ ¬monotone (λ (x : ℝ), -x)
  >> apply not_monotone_iff.mpr,
⊢ ∃ (x y : ℝ), x ≤ y ∧ -x > -y
  >> use [2, 3],
⊢ 2 ≤ 3 ∧ -2 > -3
  >> norm_num,
no goals
-/

