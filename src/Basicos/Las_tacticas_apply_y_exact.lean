-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
--    1. Importar la teoría de los números reales
--    2. Declarar x, y y z como variables sobre R.
-- ----------------------------------------------------------------------

import data.real.basic

variables (x y z : ℝ)

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    x ≤ y
--    y ≤ z
-- entonces
--    x ≤ z
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : y ≤ z)
  : x ≤ z :=
begin
  apply le_trans,
  { apply h1, },
  apply h2,
end

-- El desarrollo de la prueba es
--
--    x y z : ℝ,
--    h1 : x ≤ y,
--    h2 : y ≤ z
--    ⊢ x ≤ z
-- apply le_trans,
--    ⊢ x ≤ ?m_1
-- { apply h1 },
--    ⊢ y ≤ z
-- apply h2,
--    no goals

-- 2ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : y ≤ z)
  : x ≤ z :=
begin
  apply le_trans h1,
  apply h2,
end

-- El desarrollo de la prueba es
--
--    x y z : ℝ,
--    h1 : x ≤ y,
--    h2 : y ≤ z
--    ⊢ x ≤ z
-- apply le_trans h1,
--    ⊢ y ≤ z
-- apply h2,
--    no goals

-- 3ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : y ≤ z)
  : x ≤ z :=
by exact le_trans h1 h2

-- 4ª demostración
-- ===============

example
  (h1 : x ≤ y)
  (h2 : y ≤ z)
  : x ≤ z :=
le_trans h1 h2

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que
--    x ≤ x
-- ----------------------------------------------------------------------

-- 1ª demostración
example : x ≤ x :=
by apply le_refl

-- 2ª demostración
example : x ≤ x :=
by exact le_refl x

-- 3ª demostración
example (x : ℝ) : x ≤ x :=
le_refl x
