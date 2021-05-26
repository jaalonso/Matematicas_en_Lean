-- ---------------------------------------------------------------------
-- Ejercicio. Sean a y b números reales. Demostrar que
--    abs a - abs b ≤ abs (a - b)
-- ----------------------------------------------------------------------

import data.real.basic

variables a b c : ℝ

example : abs a - abs b ≤ abs (a - b) :=
begin
  apply sub_le_iff_le_add.mpr,
  have h1 : abs a = abs ((a - b) + b),
    by ring,
  rw h1,
  apply abs_add,
end

-- Lemas usados:
-- #check (abs_add : ∀ a b : ℝ, abs (a + b) ≤ abs a + abs b)
-- #check (sub_le_iff_le_add : a - b ≤ c ↔ a ≤ c + b)
