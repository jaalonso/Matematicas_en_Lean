-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    s ∩ t = t ∩ s
-- ----------------------------------------------------------------------

import tactic

open set

variable {α : Type*}
variables (s t u : set α)

-- 1ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
begin
  ext x,
  simp only [mem_inter_eq],
  split,
  { rintros ⟨xs, xt⟩, 
    exact ⟨xt, xs⟩ },
  { rintros ⟨xt, xs⟩, 
    exact ⟨xs, xt⟩ },
end

-- Prueba
-- ======

/-
α : Type u_1,
s t : set α
⊢ s ∩ t = t ∩ s
  >> ext x,
x : α
⊢ x ∈ s ∩ t ↔ x ∈ t ∩ s
  >> simp only [mem_inter_eq],
⊢ x ∈ s ∧ x ∈ t ↔ x ∈ t ∧ x ∈ s
  >> split,
| ⊢ x ∈ s ∧ x ∈ t → x ∈ t ∧ x ∈ s
|   >> { rintros ⟨xs, xt⟩,
| xs : x ∈ s,
| xt : x ∈ t
| ⊢ x ∈ t ∧ x ∈ s 
|   >>   exact ⟨xt, xs⟩ },
⊢ x ∈ t ∧ x ∈ s → x ∈ s ∧ x ∈ t
  >> { rintros ⟨xt, xs⟩, 
xt : x ∈ t,
xs : x ∈ s
⊢ x ∈ s ∧ x ∈ t
  >>   exact ⟨xs, xt⟩ },
no goals
-/

-- Comentarios:
-- 1. La táctica (ext x) transforma la conclusión (s = t) en 
--    (x ∈ s ↔ x ∈ t).
-- 2. Se ha usado el lema
--    + mem_inter_eq x s t : x ∈ s ∩ t = (x ∈ s ∧ x ∈ t) 

-- Comprobación:
variable (x : α)
#check @mem_inter_eq _ x s t

-- 2ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
ext $ λ x, ⟨λ ⟨xs, xt⟩, ⟨xt, xs⟩, λ ⟨xt, xs⟩, ⟨xs, xt⟩⟩

-- Comentario: La notación `f $ ...`  es equivalente a `f (...)`.

-- 3ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
by ext x; simp [and.comm]

-- 4ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
inf_comm

-- 5ª demostración
-- ===============

example : s ∩ t = t ∩ s :=
begin
  apply subset.antisymm,
  { rintros x ⟨xs, xt⟩, 
    exact ⟨xt, xs⟩ },
  { rintros x ⟨xt, xs⟩, 
    exact ⟨xs, xt⟩ },
end

-- Prueba
-- ======

/-
α : Type u_1,
s t : set α
⊢ s ∩ t = t ∩ s
  >> apply subset.antisymm,
| ⊢ s ∩ t ⊆ t ∩ s
|   >> { rintros x ⟨xs, xt⟩, 
| x : α,
| xs : x ∈ s,
| xt : x ∈ t
| ⊢ x ∈ t ∩ s
|   >>   exact ⟨xt, xs⟩ },
⊢ t ∩ s ⊆ s ∩ t
  >> { rintros x ⟨xt, xs⟩, 
x : α,
xt : x ∈ t,
xs : x ∈ s
⊢ x ∈ s ∩ t
  >>   exact ⟨xs, xt⟩ },
no goals
-/



