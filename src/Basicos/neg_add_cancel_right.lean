-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la teoría de anillos. 
-- ----------------------------------------------------------------------

import algebra.ring

-- ---------------------------------------------------------------------
-- Ejercicio 2. Crear el espacio de nombre my_ring. 
-- ----------------------------------------------------------------------

namespace my_ring

-- ---------------------------------------------------------------------
-- Ejercicio 3. Declara R una variable sobre anillos. 
-- ----------------------------------------------------------------------

variables {R : Type*} [ring R]

-- ---------------------------------------------------------------------
-- Ejercicio 4. Declarar a y b como variables sobre R. 
-- ----------------------------------------------------------------------

variables a b : R


-- 1ª demostración
-- ===============

example : (a + b) + -b = a :=
begin
  rw add_assoc,
  rw add_right_neg,
  rw add_zero,
end

-- El desarrollo de la prueba es
-- 
--    R : Type u_1,
--    _inst_1 : ring R,
--    a b : R
--    ⊢ a + b + -b = a
-- rw add_assoc,
--    ⊢ a + (b + -b) = a
-- rw add_right_neg,
--    ⊢ a + 0 = a
-- rw add_zero,
--    no goals

-- 2ª demostración
-- ===============

example : (a + b) + -b = a :=
by rw [add_assoc, add_right_neg, add_zero]

-- 3ª demostración
-- ===============

theorem neg_add_cancel_right : (a + b) + -b = a :=
calc
  (a + b) + -b 
      = a + (b + -b) : by rw add_assoc
  ... = a + 0        : by rw add_right_neg
  ... = a            : by rw add_zero

-- ---------------------------------------------------------------------
-- Ejercicio 4. Cerrar la teoría my_ring 
-- ----------------------------------------------------------------------

end my_ring
