-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la librería básica de los números reales.
-- ---------------------------------------------------------------------

import data.real.basic

-- ---------------------------------------------------------------------
-- Ejercicio 2. Crear una sección.
-- ---------------------------------------------------------------------

section

-- ---------------------------------------------------------------------
-- Ejercicio 3. Declarar que a, b y c son variables sobre los números
-- reales.
-- ---------------------------------------------------------------------

variables a b c : ℝ

-- ---------------------------------------------------------------------
-- Ejercicio 4. Calcular el tipo de a.
-- ---------------------------------------------------------------------

-- #check a

-- Comentario: Al colocar el cursor sobre check se obtiene
--    a : ℝ

-- ---------------------------------------------------------------------
-- Ejercicio 5. Calcular el tipo de a + b.
-- ---------------------------------------------------------------------

-- #check a + b

-- Comentario: Al colocar el cursor sobre check se obtiene
--    a + b : ℝ

-- ---------------------------------------------------------------------
-- Ejercicio 6. Comprobar que a es un número real.
-- ---------------------------------------------------------------------

-- #check (a : ℝ)

-- Comentario: Al colocar el cursor sobre check se obtiene
--    a : ℝ

-- ---------------------------------------------------------------------
-- Ejercicio 7. Calcular el tipo de
--    mul_comm a b
-- ---------------------------------------------------------------------

-- #check mul_comm a b

-- Comentario: Al colocar el cursor sobre check se obtiene
--    mul_comm a b : a * b = b * a

-- ---------------------------------------------------------------------
-- Ejercicio 8. Comprobar que el tipo de
--    mul_comm a b
-- es
--    a * b = b * a)
-- ---------------------------------------------------------------------

-- #check (mul_comm a b : a * b = b * a)

-- Comentario: Al colocar el cursor sobre check se obtiene
--    mul_comm a b : a * b = b * a

-- ---------------------------------------------------------------------
-- Ejercicio 9. Calcular el tipo de
--    mul_assoc c a b
-- ---------------------------------------------------------------------

-- #check mul_assoc c a b

-- Comentario: Al colocar el cursor sobre check se obtiene
--    mul_assoc c a b : c * a * b = c * (a * b)

-- ---------------------------------------------------------------------
-- Ejercicio 10. Calcular el tipo de
--    mul_comm a
-- ---------------------------------------------------------------------

-- #check mul_comm a

-- Comentario: Al colocar el cursor sobre check se obtiene
--    mul_comm a : ∀ (b : ℝ), a * b = b * a

-- ---------------------------------------------------------------------
-- Ejercicio 11. Calcular el tipo de
--    mul_comm
-- ---------------------------------------------------------------------

-- #check mul_comm

-- Comentario: Al colocar el cursor sobre check se obtiene
--    mul_comm : ∀ (a b : ?M_1), a * b = b * a

-- ---------------------------------------------------------------------
-- Ejercicio 12. Calcular el tipo de
--    @mul_comm
-- ---------------------------------------------------------------------

-- #check @mul_comm

-- Comentario: Al colocar el cursor sobre check se obtiene
--    mul_comm : ∀ {G : Type u_1} [_inst_1 : comm_semigroup G] (a b : G),
--               a * b = b * a

end
