-- ---------------------------------------------------------------------
-- Ejercicio . Demostrar que si f es una función suprayectiva de ℝ en ℝ,
-- entonces existe un x tal que (f x)^2 = 4.
-- ----------------------------------------------------------------------

import data.real.basic

open function

example 
  {f : ℝ → ℝ} 
  (h : surjective f) 
  : ∃ x, (f x)^2 = 4 :=
begin
  cases h 2 with x hx,
  use x,
  rw hx,
  norm_num,
end

-- La prueba es
-- 
-- f : ℝ → ℝ,
-- h : surjective f
-- ⊢ ∃ (x : ℝ), f x ^ 2 = 4
--    >> cases h 2 with x hx,
-- x : ℝ,
-- hx : f x = 2
-- ⊢ ∃ (x : ℝ), f x ^ 2 = 4
--    >> use x,
-- ⊢ f x ^ 2 = 4
--    >> rw hx,
-- ⊢ 2 ^ 2 = 4
--    >> norm_num,
-- no goals

