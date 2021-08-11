-- ---------------------------------------------------------------------
-- Ejercicio. Sean a, b y c números reales. Calcular los tipos de
--    le_max_left a b
--    le_max_right a b
--    @max_le ℝ _ a b c
-- ----------------------------------------------------------------------

import data.real.basic

variables a b c : ℝ

-- #check le_max_left a b
-- #check le_max_right a b
-- #check @max_le ℝ _ a b c

-- Comentario al colocar el cursor sobre check se obtiene
--    le_max_left a b : a ≤ max a b
--    le_max_right a b : b ≤ max a b
--    max_le : a ≤ c → b ≤ c → max a b ≤ c
