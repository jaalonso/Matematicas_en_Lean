-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
--    1. Importar la teoría de los números reales
--    2. Declarar a, b y c como variables sobre R.
-- ----------------------------------------------------------------------

import data.real.basic

variables a b c : ℝ

-- ---------------------------------------------------------------------
-- Ejercicio 2. Calcular el tipo de las siguientes expresiones:
--    + le_refl
--    + le_trans
--    + lt_of_le_of_lt
--    + lt_of_lt_of_le
--    + lt_trans
-- ----------------------------------------------------------------------


-- #check (le_refl  : ∀ a, a ≤ a)
-- #check (le_trans : a ≤ b → b ≤ c → a ≤ c)
-- #check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
-- #check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
-- #check (lt_trans : a < b → b < c → a < c)
