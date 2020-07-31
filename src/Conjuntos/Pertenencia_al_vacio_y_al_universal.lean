-- ---------------------------------------------------------------------
-- Ejercicio. Abrir el espacion de nombres set. 
-- ----------------------------------------------------------------------

import tactic

open set

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar ningún elemento pertenece al vacío.
-- ----------------------------------------------------------------------

example (x : ℕ) : x ∉ (∅ : set ℕ) :=
not_false

example (x : ℕ) (h : x ∈ (∅ : set ℕ)) : false :=
h

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar tofos los elementos pertenecen al universal.
-- ----------------------------------------------------------------------

example (x : ℕ) : x ∈ (univ : set ℕ) :=
trivial
