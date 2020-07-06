-- ---------------------------------------------------------------------
-- Ejercicio . Demostrar que, para todo númeo real a, 
--    0 ≤ a^2
-- ----------------------------------------------------------------------

import data.real.basic
import tactic

example (a : ℝ) : 0 ≤ a^2 :=
begin
  -- library_search,
  exact pow_two_nonneg a,
end

-- Notas:
-- + Nota 1: Al colocar el cursor sobre library_search (después de descomentar 
--   la línea) escribe el mensaje
--      Try this: exact pow_two_nonneg a
-- + Nota 2: Para usar library_search hay que importar tactic.
