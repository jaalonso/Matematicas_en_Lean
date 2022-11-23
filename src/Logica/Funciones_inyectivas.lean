-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la librería de números reales.
-- 2. Abrir el espacio de nombre de las funciones.
-- ----------------------------------------------------------------------

import data.real.basic                                               -- 1

open function                                                        -- 2

variable {c : ℝ}

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que, para todo c la función
--    f(x) = x + c
-- es inyectiva
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  : injective (λ x, x + c) :=
begin
  assume x1 : ℝ,
  assume x2 : ℝ,
  assume h1 : (λ x, x + c) x1 = (λ x, x + c) x2,
  have h2 : x1 + c = x2 + c := h1,
  show x1 = x2,
    by exact (add_left_inj c).mp h2,
end

-- 2ª demostración
-- ===============

example
  : injective (λ x, x + c) :=
begin
  intros x1 x2 h,
  change x1 + c = x2 + c at h,
  apply add_right_cancel h,
end

-- 3ª demostración
-- ===============

example
  : injective (λ x, x + c) :=
begin
  intros x1 x2 h,
  apply (add_left_inj c).mp,
  exact h,
end

-- 4ª demostración
-- ===============

example
  : injective (λ x, x + c) :=
λ x1 x2 h, (add_left_inj c).mp h

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que, para todo c distinto de cero la función
--    f(x) = x * c
-- es inyectiva
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (h : c ≠ 0)
  : injective (λ x, c * x) :=
begin
  assume x1 : ℝ,
  assume x2 : ℝ,
  assume h1 : (λ x, c * x) x1 = (λ x, c * x) x2,
  have h2 : c * x1 = c * x2 := h1,
  show x1 = x2,
    by exact (mul_right_inj' h).mp h1,
end

-- 2ª demostración
-- ===============

example
  (h : c ≠ 0)
  : injective (λ x, c * x) :=
begin
  intros x1 x2 h',
  dsimp at h',
  apply mul_left_cancel₀ h,
  exact h',
end

-- 3ª demostración
-- ===============

example
  (h : c ≠ 0)
  : injective (λ x, c * x) :=
begin
  intros x1 x2 h',
  dsimp at h',
  exact (mul_right_inj' h).mp h'
end

-- 3ª demostración
-- ===============

example
  {c : ℝ}
  (h : c ≠ 0)
  : injective (λ x, c * x) :=
λ x1 x2 h', mul_left_cancel₀ h h'
