-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la librería de grupos 
-- ----------------------------------------------------------------------

import algebra.group

-- ---------------------------------------------------------------------
-- Ejercicio 2. Declarar G como un tipo sobre grupos.
-- ----------------------------------------------------------------------

variables (G : Type*) [group G]

-- ---------------------------------------------------------------------
-- Ejercicio 3. Comprobar que G verifica los axiomas de los grupos 
-- ----------------------------------------------------------------------

#check (mul_assoc :    ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul :      ∀ a : G,     1 * a = a)
#check (mul_left_inv : ∀ a : G,     a⁻¹ * a = 1)  

