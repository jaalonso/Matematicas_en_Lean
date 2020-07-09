-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar la propiedad transitiva de la inclusión de
-- conjuntos.  
-- ----------------------------------------------------------------------

import tactic

variables {α : Type*} (r s t : set α)

-- 1ª demostración
-- ===============

example : r ⊆ s → s ⊆ t → r ⊆ t :=
begin
  intros rs st x xr,
  apply st,
  apply rs,
  exact xr 
end

-- El desarrollo es
-- 
-- α : Type u_1,
-- r s t : set α
-- ⊢ r ⊆ s → s ⊆ t → r ⊆ t
--    >> intros rs st x xr,
-- rs : r ⊆ s,
-- st : s ⊆ t,
-- x : α,
-- xr : x ∈ r
-- ⊢ x ∈ t
--    >> apply st,
-- ⊢ x ∈ s
--    >> apply rs,
-- ⊢ x ∈ r
--    >> exact xr 
-- no goals

-- 2ª demostración
-- ===============

example : r ⊆ s → s ⊆ t → r ⊆ t :=
λ rs st x xr, st (rs xr)

