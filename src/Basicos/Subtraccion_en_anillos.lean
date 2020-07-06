-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
--    1. Importar la teoría de anillos.
--    2. Crear el espacio de nombres my_ring
--    3. Declarar R como una variable sobre anillos.
--    4. Declarar a y b como variables sobre R. 
-- ----------------------------------------------------------------------

import algebra.ring            -- 1
namespace my_ring              -- 2
variables {R : Type*} [ring R] -- 3
variables (a b : R)            -- 4

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    a - b = a + -b
-- ----------------------------------------------------------------------

-- 1ª demostración
theorem sub_eq_add_neg  : a - b = a + -b :=
rfl

-- 2ª demostración
example : a - b = a + -b :=
by reflexivity

end my_ring
