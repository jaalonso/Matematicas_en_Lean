-- ---------------------------------------------------------------------
-- Ejercicio 1. Demostrar el teorema facil que afirma que 2 + 3 = 5.
-- ---------------------------------------------------------------------

theorem facil : 2 + 3 = 5 := rfl

-- Comentarios:
-- 1. Para activar la ventana de objetivos (*Lean Goal*) se escribe
--    C-c C-g
-- 2. Se desactiva volviendo a escribir C-c C-g
-- 3. La táctica rfl (ver https://bit.ly/2BYbiBH) comprueba que 2+3 y 5
--    son iguales por definición.

-- ---------------------------------------------------------------------
-- Ejercicio 2. Calcular el tipo de facil
-- ---------------------------------------------------------------------

-- #check facil

-- Comentario: Colocando el cursor sobre check se obtiene
--    facil : 2 + 3 = 5

-- ---------------------------------------------------------------------
-- Ejercicio 3. Enunciar el teorema dificil que afirma que se verifica
-- el último teorema de Fermat, omitiendo la demostración.
-- ---------------------------------------------------------------------

/-
def ultimo_teorema_de_Fermat :=
  ∀ x y z n : ℕ, n > 2 → x * y * z ≠ 0 → x^n + y^n ≠ z^n

theorem dificil : ultimo_teorema_de_Fermat :=
sorry
-/

-- Comentarios:
-- 1. La palabra sorry se usa para omitir la demostración.
-- 2. Se puede verificar la teoría pulsando
--       C-x ! l
--    Se obtiene
--       31   1 warning         declaration 'dificil' uses sorry

-- ---------------------------------------------------------------------
-- Ejercicio 3. Calcular el tipo de dificil.
-- ---------------------------------------------------------------------

-- #check dificil

-- Comentario: Colocando el cursor sobre check se obtiene
--    dificil : ultimo_teorema_de_Fermat
