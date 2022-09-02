-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones
--    1. Importar la teoría de exponeciales y logaritmos.
--    2. Abrir la teoría de los reales
--    3. Declarar a y b como variables sobre los reales.
-- ----------------------------------------------------------------------

import analysis.special_functions.log.basic -- 1
open real                                   -- 2
variables (a b : ℝ)                         -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Calcular el tipo del lema exp_le_exp
-- ----------------------------------------------------------------------

-- #check @exp_le_exp a b

-- Comentario: Al colocar el cursor sobre check se obtiene
--    exp_le_exp : a.exp ≤ b.exp ↔ a ≤ b

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si
--    a ≤ b
--    exp a ≤ exp b
-- ----------------------------------------------------------------------

-- 1ª demostración
example
  (h : a ≤ b)
  : exp a ≤ exp b :=
begin
  rw exp_le_exp,
  exact h
end

-- 2ª demostración
example
  (h : a ≤ b)
  : exp a ≤ exp b :=
exp_le_exp.mpr h

-- Nota: Con mpr se indica en modus pones inverso. Por ejemplo, si
-- h: A ↔ B, entonces h.mpr es B → A y h.mp es A → B
