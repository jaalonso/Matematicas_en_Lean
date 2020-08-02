-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    s ⊆ f ⁻¹' (f '' s)
-- ----------------------------------------------------------------------

import data.set.function

universes u v
variable  α : Type u
variable  β : Type v
variable  f : α → β
variables s t : set α

example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  show f x ∈ f '' s,
  use [x, xs],
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
s : set α
⊢ s ⊆ f ⁻¹' (f '' s)
  >> intros x xs,
x : α,
xs : x ∈ s
⊢ x ∈ f ⁻¹' (f '' s)
  >> show f x ∈ f '' s,
⊢ f x ∈ f '' s
  >> use [x, xs],
no goals
-/

-- 2ª demostración
-- ===============

example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  show f x ∈ f '' s,
  apply set.mem_image_of_mem f xs,
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
s : set α
⊢ s ⊆ f ⁻¹' (f '' s)
  >> intros x xs,
x : α,
xs : x ∈ s
⊢ x ∈ f ⁻¹' (f '' s)
  >> show f x ∈ f '' s,
⊢ f x ∈ f '' s
  >> apply set.mem_image_of_mem f xs,
no goals
-/

-- Comentario: Se ha usado el lema
-- + set.mem_image_of_mem : x ∈ a → f x ∈ f '' a
