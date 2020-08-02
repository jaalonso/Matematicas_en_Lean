-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f '' s ⊆ t ↔ s ⊆ f ⁻¹' t
-- ----------------------------------------------------------------------

import data.set.function

universes u v
variable  α : Type u
variable  β : Type v
variable  f : α → β
variables (s : set α) (t : set β)

open set

example : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t :=
begin
  split,
  { intros h x xs,
    show f x ∈ t,
      { calc f x ∈ f '' s : mem_image_of_mem f xs
             ... ⊆ t      : h }},  
  { intros h y hy,
    rcases hy with ⟨x,xs,fxy⟩,
    rw ← fxy,
    apply h,
    exact xs },  
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
s : set α,
t : set β
⊢ f '' s ⊆ t ↔ s ⊆ f ⁻¹' t
  >> split,
| ⊢ f '' s ⊆ t → s ⊆ f ⁻¹' t
|   >> { intros h x xs,
| h : f '' s ⊆ t,
| x : α,
| xs : x ∈ s
| ⊢ x ∈ f ⁻¹' t
|   >>   show f x ∈ t,
|   >>     { calc f x ∈ f '' s : mem_image_of_mem f xs
|   >>            ... ⊆ t      : h }},
⊢ s ⊆ f ⁻¹' t → f '' s ⊆ t  
  >> { intros h y hy,
h : s ⊆ f ⁻¹' t,
y : β,
hy : y ∈ f '' s
⊢ y ∈ t
  >>   rcases hy with ⟨x,xs,fxy⟩,
x : α,
xs : x ∈ s,
fxy : f x = y
⊢ y ∈ t
  >>   rw ← fxy,
⊢ f x ∈ t
  >>   apply h,
⊢ x ∈ s
  >>   exact xs },
no goals  
-/

