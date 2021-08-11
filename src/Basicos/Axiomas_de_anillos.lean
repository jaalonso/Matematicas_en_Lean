-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la librería de anillos.
-- ----------------------------------------------------------------------

import algebra.ring

-- ---------------------------------------------------------------------
-- Ejercicio 2. Declarar R como un tipo sobre los anillos.
-- ----------------------------------------------------------------------

variables (R : Type*) [ring R]

-- ---------------------------------------------------------------------
-- Ejercicio 3. Comprobar que R verifica los axiomas de los anillos.
-- ----------------------------------------------------------------------

-- #check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
-- #check (add_comm : ∀ a b : R, a + b = b + a)
-- #check (zero_add : ∀ a : R, 0 + a = a)
-- #check (add_left_neg : ∀ a : R, -a + a = 0)
-- #check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
-- #check (mul_one : ∀ a : R, a * 1 = a)
-- #check (one_mul : ∀ a : R, 1 * a = a)
-- #check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
-- #check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
