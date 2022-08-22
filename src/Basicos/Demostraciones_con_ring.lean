-- ---------------------------------------------------------------------
-- Ejercicio. Sean a, b, c y números reales. Demostrar, con la táctica
-- ring, que
--    (c * b) * a = b * (a * c)
--    (a + b) * (a + b) = a * a + 2 * (a * b) + b * b
--    (a + b) * (a - b) = a^2 - b^2
-- Además, si
--    c = d * a + b
--    b = a * d
-- entonces
--    c = 2 * a * d
-- ---------------------------------------------------------------------

import data.real.basic

variables a b c d : ℝ

example : (c * b) * a = b * (a * c) :=
by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
by ring

example : (a + b) * (a - b) = a^2 - b^2 :=
by ring

example
  (h1 : c = d * a + b)
  (h2 : b = a * d)
  : c = 2 * a * d :=
begin
  rw [h1, h2],
  ring
end
