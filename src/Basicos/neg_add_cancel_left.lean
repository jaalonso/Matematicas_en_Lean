-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la teoría de anillos. 
-- ----------------------------------------------------------------------

import algebra.ring

-- ---------------------------------------------------------------------
-- Ejercicio 2. Crear el espacio de nombre my_ring
-- ----------------------------------------------------------------------

namespace my_ring

-- ---------------------------------------------------------------------
-- Ejercicio 3. Declarar R como una variable sobre anillos. 
-- ----------------------------------------------------------------------

variables {R : Type*} [ring R]

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que para todo a, b ∈ R,
--    -a + (a + b) = b
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (a b : R) 
  : -a + (a + b) = b :=
calc
  -a + (a + b) = (-a + a) + b : by rw ← add_assoc
           ... = 0 + b        : by rw add_left_neg
           ... = b            : by rw zero_add

-- 2ª demostración 
-- ===============

theorem neg_add_cancel_left 
  (a b : R) 
  : -a + (a + b) = b :=
by rw [←add_assoc, add_left_neg, zero_add]

-- El desarrollo de la prueba es
-- 
--    R : Type u_1,
--    _inst_1 : ring R,
--    a b : R
--    ⊢ -a + (a + b) = b
-- rw ← add_assoc, 
--    ⊢ -a + a + b = b
-- rw add_left_neg, 
--    ⊢ 0 + b = b
-- rw zero_add,
--    no goals

-- ---------------------------------------------------------------------
-- Ejercicio 6. Cerrar el espacio de nombre my_ring. 
-- ----------------------------------------------------------------------

end my_ring
