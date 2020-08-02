import data.set.function

open set function

universes u v
variable  α : Type u
variable  β : Type v
variable  f : α → β
variables s t : set α
variables u v : set β

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es inyectiva, entonces
--    f ⁻¹' (f '' s) ⊆ s 
-- ----------------------------------------------------------------------

example 
  (h : injective f) 
  : f ⁻¹' (f '' s) ⊆ s :=
begin
  intros x hx,
  have h1 : f x ∈ f '' s := hx,
  rcases h1 with ⟨y, ys, fyfx⟩,
  have h2 : y = x := h fyfx,
  rw ← h2,
  exact ys,
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
s : set α,
h : injective f
⊢ f ⁻¹' (f '' s) ⊆ s
  >> intros x hx,
x : α,
hx : x ∈ f ⁻¹' (f '' s)
⊢ x ∈ s
  >> have h1 : f x ∈ f '' s := hx,
h1 : f x ∈ f '' s
⊢ x ∈ s
  >> rcases h1 with ⟨y, ys, fyfx⟩,
y : α,
ys : y ∈ s,
fyfx : f y = f x
⊢ x ∈ s
  >> have h2 : y = x := h fyfx,
h2 : y = x
⊢ x ∈ s
  >> rw ← h2,
⊢ y ∈ s
  >> exact ys,
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f '' (f⁻¹' u) ⊆ u
-- ----------------------------------------------------------------------

example : f '' (f⁻¹' u) ⊆ u :=
begin
  rintros y ⟨x, hxu, fxy⟩,
  rw ← fxy,
  exact hxu,
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
u : set β
⊢ f '' (f ⁻¹' u) ⊆ u
  >> rintros y ⟨x, hxu, fxy⟩,
y : β,
x : α,
hxu : x ∈ f ⁻¹' u,
fxy : f x = y
⊢ y ∈ u
  >> rw ← fxy,
⊢ f x ∈ u
  >> exact hxu,
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es suprayectiva, entonces
--    u ⊆ f '' (f⁻¹' u)
-- ----------------------------------------------------------------------

example 
  (h : surjective f) 
  : u ⊆ f '' (f⁻¹' u) :=
begin
  sorry
end

example (h : s ⊆ t) : f '' s ⊆ f '' t :=
sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v :=
sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
sorry

example (h : injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) :=
sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u :=
sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
sorry
