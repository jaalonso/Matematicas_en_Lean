-- ---------------------------------------------------------------------
-- Ejercicio. Declarar α como una variables de tipos habitados.
-- ----------------------------------------------------------------------

variables {α : Type*} [inhabited α]

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de
--     default α
-- ----------------------------------------------------------------------

-- #check default α

-- Comntario: Al colocar el cursor sobre check se obtiene
--    default α : α

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar P como un predicado sobre α tal que existe algún
-- elemento que verifica P.
-- ----------------------------------------------------------------------

variables (P : α → Prop) (h : ∃ x, P x)

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular el tipo de
--    classical.some h
-- ----------------------------------------------------------------------

-- #check classical.some h

-- Comntario: Al colocar el cursor sobre check se obtiene
--    classical.some h : α

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    P (classical.some h)
-- ----------------------------------------------------------------------

example : P (classical.some h) :=
classical.some_spec h
