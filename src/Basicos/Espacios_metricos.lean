-- ---------------------------------------------------------------------
-- Ejercicio 1. Ejecuta las siguientes acciones
-- 1. Importar la teoría de espacios métricos.
-- 2. Declarar X como un tipo sobre espacios métricos.
-- 3. Declarar x, y y z como variables sobre X.
-- ----------------------------------------------------------------------

import topology.metric_space.basic       -- 1
variables {X : Type*} [metric_space X]   -- 2
variables x y z : X                      -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Calcular el tipo de las siguientes expresiones
--    dist_self x
--    dist_comm x y
--    dist_triangle x y z
-- ----------------------------------------------------------------------

-- #check dist_self x
-- #check dist_comm x y
-- #check dist_triangle x y z

-- Comentario: Al colocar el cursor sobre check se obtiene
--    dist_self x : dist x x = 0
--    dist_comm x y : dist x y = dist y x
--    dist_triangle x y z : dist x z ≤ dist x y + dist y z
