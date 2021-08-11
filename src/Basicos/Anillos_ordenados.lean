-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones
--    1. Importar la teoría de los anillos ordenados.
--    2. Declarar R como un tipo sobre los anillos ordenados.
--    3. Declarar a y b como variables sobre R.
-- ----------------------------------------------------------------------

import algebra.ordered_ring              -- 1
variables {R : Type*} [ordered_ring R]   -- 2
variables a b : R                        -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Calcular el tipo de las siguientes expresiones
--    @add_le_add_left R _ a b
--    @mul_pos R _ a b
--    zero_ne_one
--    @mul_nonneg R _ a b
-- ----------------------------------------------------------------------

-- #check @add_le_add_left
-- #check @mul_pos R _ a b
-- #check zero_ne_one
-- #check @mul_nonneg R _ a b

-- Comentario: Al colocar el cursor sobre check se obtiene
--    add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b
--    mul_pos : 0 < a → 0 < b → 0 < a * b
--    zero_ne_one : 0 ≠ 1
--    mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b
