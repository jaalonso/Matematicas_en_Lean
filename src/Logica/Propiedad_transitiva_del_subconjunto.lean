-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar la propiedad transitiva de la inclusión de
-- conjuntos.
-- ----------------------------------------------------------------------

import tactic

variables {α : Type*}
variables r s t : set α

-- 1ª demostración
-- ===============

example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
begin
  assume x,
  assume xr : x ∈ r,
  have h1 : x ∈ s := rs xr,
  show x ∈ t,
    by exact st h1,
end

-- 2ª demostración
-- ===============

example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
begin
  intros x xr,
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

-- 3ª demostración
-- ===============

example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
λ x xr, st (rs xr)

-- 4ª demostración
-- ===============

example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
-- by library_search
set.subset.trans rs st

-- 5ª demostración
-- ===============

example
  (rs : r ⊆ s)
  (st : s ⊆ t)
  : r ⊆ t :=
-- by hint
by tauto
