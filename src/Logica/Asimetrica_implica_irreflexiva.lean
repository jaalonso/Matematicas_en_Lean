-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que para tododos par de numero reales a y b, si 
-- a < b entonces no se tiene que b < a.
-- ----------------------------------------------------------------------

import data.real.basic

variables a b : ℝ

example 
  (h : a < b) 
  : ¬ b < a :=
begin
  intro h',
  have : a < a,
    from lt_trans h h',
  apply lt_irrefl a this,
end

-- La prueba es
-- 
-- a b : ℝ,
-- h : a < b
-- ⊢ ¬b < a
--    >>   intro h',
-- h' : b < a
-- ⊢ false
--    >>   have : a < a,
--    >>     from lt_trans h h',
-- this : a < a
-- ⊢ false
--    >>   apply lt_irrefl a this,
-- no goals
