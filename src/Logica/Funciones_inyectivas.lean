-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la librería de números reales.
-- 2. Abrir el espacio de nombre de las funciones. 
-- ----------------------------------------------------------------------

import data.real.basic                                               -- 1

open function                                                        -- 2

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que, para todo c la función
--    f(x) = x + c
-- es inyectiva
-- ----------------------------------------------------------------------

example 
  (c : ℝ) 
  : injective (λ x, x + c) :=
begin
  intros x₁ x₂ h',
  change x₁ + c = x₂ + c at h',
  apply add_right_cancel h',
end

-- Su desarrollo es
-- 
-- c : ℝ
-- ⊢ injective (λ (x : ℝ), x + c)
--    >> intros x₁ x₂ h',
-- c x₁ x₂ : ℝ,
-- h' : (λ (x : ℝ), x + c) x₁ = (λ (x : ℝ), x + c) x₂
-- ⊢ x₁ = x₂
--    >> change x₁ + c = x₂ + c at h',
-- c x₁ x₂ : ℝ,
-- h' : x₁ + c = x₂ + c
-- ⊢ x₁ = x₂
--    >> apply add_right_cancel h'
-- no goals

-- 2ª demostración
-- ===============

example 
  (c : ℝ) 
  : injective (λ x, x + c) :=
begin
  intros x₁ x₂ h',
  apply (add_left_inj c).mp,
  exact h', 
end

-- Su desarrollo es
-- 
-- c : ℝ
-- ⊢ injective (λ (x : ℝ), x + c)
--    >> intros x₁ x₂ h',
-- c x₁ x₂ : ℝ,
-- h' : (λ (x : ℝ), x + c) x₁ = (λ (x : ℝ), x + c) x₂
-- ⊢ x₁ = x₂
--    >> apply (add_left_inj c).mp,
-- ⊢ x₁ + c = x₂ + c
--    >> exact h', 
-- no goals

-- 3ª demostración
-- ===============

example 
  (c : ℝ) 
  : injective (λ x, x + c) :=
λ x₁ x₂ h', (add_left_inj c).mp h'


-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que, para todo c distinto de cero la función
--    f(x) = x * c
-- es inyectiva
-- ----------------------------------------------------------------------

example 
  {c : ℝ} 
  (h : c ≠ 0) 
  : injective (λ x, c * x) :=
begin
  intros x₁ x₂ h',
  change c * x₁ = c * x₂ at h',
  apply mul_left_cancel' h h',
end

-- Su desarrollo es
--
-- c : ℝ,
-- h : c ≠ 0
-- ⊢ injective (λ (x : ℝ), c * x)
--    >> intros x₁ x₂ h',
-- x₁ x₂ : ℝ,
-- h' : (λ (x : ℝ), c * x) x₁ = (λ (x : ℝ), c * x) x₂
-- ⊢ x₁ = x₂
--    >> change c * x₁ = c * x₂ at h',
-- h' : c * x₁ = c * x₂
-- ⊢ x₁ = x₂
--    >> apply mul_left_cancel' h h',
-- no goals

-- 2ª demostración
-- ===============

example 
  {c : ℝ} 
  (h : c ≠ 0) 
  : injective (λ x, c * x) :=
begin
  intros x₁ x₂ h',
  apply mul_left_cancel' h,
  exact h',
end

-- Su desarrollo es
-- 
-- c : ℝ,
-- h : c ≠ 0
-- ⊢ injective (λ (x : ℝ), c * x)
--    >> intros x₁ x₂ h',
-- x₁ x₂ : ℝ,
-- h' : (λ (x : ℝ), c * x) x₁ = (λ (x : ℝ), c * x) x₂
-- ⊢ x₁ = x₂
--    >> apply mul_left_cancel' h,
-- ⊢ c * x₁ = c * x₂
--    >> exact h',
-- no goals

-- 3ª demostración
-- ===============

example 
  {c : ℝ} 
  (h : c ≠ 0) 
  : injective (λ x, c * x) :=
λ x₁ x₂ h', mul_left_cancel' h h'
