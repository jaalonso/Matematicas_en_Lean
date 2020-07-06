-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
--    1. Importar la teoría de anillos.
--    2. Crear el espacio de nombres my_ring
--    3. Declarar R como una variable sobre anillos.
--    4. Declarar a como variable sobre R. 
-- ----------------------------------------------------------------------

import algebra.ring            -- 1
namespace my_ring              -- 2
variables {R : Type*} [ring R] -- 3
variables (a : R)              -- 4

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--     a - a = 0
-- ----------------------------------------------------------------------


theorem self_sub : a - a = 0 :=
calc
  a - a = a + -a : by reflexivity
  ...   = 0      : by rw add_right_neg

end my_ring
