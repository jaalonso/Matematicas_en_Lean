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
--    1 + 1 = 2
-- ----------------------------------------------------------------------

lemma one_add_one_eq_two : 1 + 1 = (2 : R) :=
by refl

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--    2 * a = a + a
-- ----------------------------------------------------------------------

theorem two_mul : 2 * a = a + a :=
calc
  2 * a = (1 + 1) * a   : by rw one_add_one_eq_two
  ...   = 1 * a + 1 * a : by rw add_mul
  ...   = a + a         : by rw one_mul

end my_ring
