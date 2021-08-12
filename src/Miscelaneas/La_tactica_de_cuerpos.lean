-- La_tactica_de_cuerpos.lean
-- La táctica de cuerpos
-- José A. Alonso Jiménez
-- Sevilla, 12 de agosto de 2021
-- ---------------------------------------------------------------------

import data.complex.basic
import tactic

example (a b c d x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
  a + b / x + c / x^2 + d / x^3 = a + x⁻¹ * (y * b / y + (d / x + c) / x) :=
begin
  field_simp,
  ring,
end
