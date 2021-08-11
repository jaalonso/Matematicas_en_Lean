-- ---------------------------------------------------------------------
-- Ejercicio. Sean a, b y c números reales. Calcular los tipos de
--    min_le_left a b
--    min_le_right a b
--    @le_min ℝ _ a b c
-- ----------------------------------------------------------------------

import data.real.basic

variables a b c : ℝ

-- #check min_le_left a b
-- #check min_le_right a b
-- #check @le_min ℝ _ a b c

-- Comentario al colocar el cursor sobre check se obtiene
--    min_le_left a b : min a b ≤ a
--    min_le_right a b : min a b ≤ b
--    le_min : c ≤ a → c ≤ b → c ≤ min a b
