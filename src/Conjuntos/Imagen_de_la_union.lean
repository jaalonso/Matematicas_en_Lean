-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f '' (s ∪ t) = (f '' s) ∪ (f '' t) 
-- ----------------------------------------------------------------------

import data.set.function

universes u v
variable  α : Type u
variable  β : Type v
variable  f : α → β
variables s t : set α

example : f '' (s ∪ t) = (f '' s) ∪ (f '' t) :=
begin
  ext y, 
  split,
  { rintros ⟨x, xs | xt, rfl⟩,
    { left, 
      use [x, xs] },
    { right, 
      use [x, xt] }},
  { rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩),
    { use [x, or.inl xs] },
    { use [x, or.inr xt] }},
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
s t : set α
⊢ f '' (s ∪ t) = f '' s ∪ f '' t
  >> ext y, 
y : β
⊢ y ∈ f '' (s ∪ t) ↔ y ∈ f '' s ∪ f '' t
  >> split,
| ⊢ y ∈ f '' (s ∪ t) → y ∈ f '' s ∪ f '' t
|   >> { rintros ⟨x, xs | xt, rfl⟩,
| | ⊢ f x ∈ f '' s ∪ f '' t
| |   >>   { left,
| | ⊢ f x ∈ f '' s 
| |   >>     use [x, xs] },
| ⊢ f x ∈ f '' s ∪ f '' t
|   >>   { right, 
| ⊢ f x ∈ f '' t
|   >>     use [x, xt] }},
⊢ y ∈ f '' s ∪ f '' t → y ∈ f '' (s ∪ t)
  >> { rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩),
| x : α,
| xs : x ∈ s
| ⊢ f x ∈ f '' (s ∪ t)
|   >>   { use [x, or.inl xs] },
xt : x ∈ t
⊢ f x ∈ f '' (s ∪ t)
  >>   { use [x, or.inr xt] }},
no goals
-/

