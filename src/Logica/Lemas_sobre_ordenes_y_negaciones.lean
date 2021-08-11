-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones
-- 1. Importar la librería de los reales.
-- 2. Declarar a y b como variables sobre los reales.
-- ----------------------------------------------------------------------

import data.real.basic

variables a b : ℝ

-- ---------------------------------------------------------------------
-- Ejercicio 2. Calcular el tipo de las siguientes expresiones.
--    @not_le_of_gt ℝ _ a b
--    @not_lt_of_ge ℝ _ a b
--    @lt_of_not_ge ℝ _ a b
--    @le_of_not_gt ℝ _ a b
-- ----------------------------------------------------------------------

-- #check @not_le_of_gt ℝ _ a b
-- #check @not_lt_of_ge ℝ _ a b
-- #check @lt_of_not_ge ℝ _ a b
-- #check @le_of_not_gt ℝ _ a b

-- Comentario: Colocando el cursor sobre check se obtiene
--    not_le_of_gt : a > b → ¬ a ≤ b
--    not_lt_of_ge : a ≥ b → ¬ a < b
--    lt_of_not_ge : ¬ a ≥ b → a < b
--    le_of_not_gt : ¬ a > b → a ≤ b
