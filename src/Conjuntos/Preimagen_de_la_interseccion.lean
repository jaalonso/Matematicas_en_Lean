-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v 
-- ----------------------------------------------------------------------

import data.set.function

universes u v
variable  α : Type u
variable  β : Type v
variable  f : α → β
variables u v : set β

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by { ext, refl }
