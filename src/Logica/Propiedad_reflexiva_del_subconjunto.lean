-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que para cualquier conjunto s, s ⊆ s.
-- ----------------------------------------------------------------------

import tactic

variables {α : Type*} (s : set α)

-- 1ª demostración
-- ===============

example : s ⊆ s :=
begin
  intros x xs,
  exact xs,
end

-- 2ª demostración
-- ===============

example : s ⊆ s :=
λ x (xs : x ∈ s), xs
