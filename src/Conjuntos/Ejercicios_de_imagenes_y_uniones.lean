import data.set.lattice

open set function

universes u1 u2 u3
variable  {α : Type u1}
variable  {β : Type u2}
variable  {I : Type u3}
variable  f : α → β
variable  A : I → set α
variable  B : I → set β

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f '' (⋃ i, A i) = ⋃ i, f '' A i
-- ----------------------------------------------------------------------

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
begin
  ext y, 
  simp,
  split,
  { rintros ⟨x, ⟨i, xAi⟩, fxeq⟩,
    use [i, x, xAi, fxeq] },
  { rintros ⟨i, x, xAi, fxeq⟩,
    exact ⟨x, ⟨i, xAi⟩, fxeq⟩ },
end

-- Prueba
-- ======

/-
α : Type u1,
β : Type u2,
I : Type u3,
f : α → β,
A : I → set α
⊢ (f '' ⋃ (i : I), A i) = ⋃ (i : I), f '' A i
  >> ext y, 
y : β
⊢ (y ∈ f '' ⋃ (i : I), A i) ↔ y ∈ ⋃ (i : I), f '' A i
  >> simp,
⊢ (∃ (x : α), (∃ (i : I), x ∈ A i) ∧ f x = y) ↔ 
  ∃ (i : I) (x : α), x ∈ A i ∧ f x = y
  >> split,
| ⊢ (∃ (x : α), (∃ (i : I), x ∈ A i) ∧ f x = y) → 
|   (∃ (i : I) (x : α), x ∈ A i ∧ f x = y)
|   >> { rintros ⟨x, ⟨i, xAi⟩, fxeq⟩,
| x : α,
| fxeq : f x = y,
| i : I,
| xAi : x ∈ A i
| ⊢ ∃ (i : I) (x : α), x ∈ A i ∧ f x = y
|   >>   use [i, x, xAi, fxeq] },
⊢ (∃ (i : I) (x : α), x ∈ A i ∧ f x = y) → 
  (∃ (x : α), (∃ (i : I), x ∈ A i) ∧ f x = y)
  >> { rintros ⟨i, x, xAi, fxeq⟩,
i : I,
x : α,
xAi : x ∈ A i,
fxeq : f x = y
⊢ ∃ (x : α), (∃ (i : I), x ∈ A i) ∧ f x = y
  >>   exact ⟨x, ⟨i, xAi⟩, fxeq⟩ },
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i
-- ----------------------------------------------------------------------

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
begin
  intro y, 
  simp,
  intros x h fxeq i,
  use [x, h i, fxeq],
end

-- Prueba
-- ======

/-
α : Type u1,
β : Type u2,
I : Type u3,
f : α → β,
A : I → set α
⊢ (f '' ⋂ (i : I), A i) ⊆ ⋂ (i : I), f '' A i
  >> intro y, 
y : β
⊢ (y ∈ f '' ⋂ (i : I), A i) → (y ∈ ⋂ (i : I), f '' A i)
  >> simp,
⊢ ∀ (x : α), (∀ (i : I), x ∈ A i) → f x = y → 
  ∀ (i : I), ∃ (x : α), x ∈ A i ∧ f x = y
  >> intros x h fxeq i,
x : α,
h : ∀ (i : I), x ∈ A i,
fxeq : f x = y,
i : I
⊢ ∃ (x : α), x ∈ A i ∧ f x = y
  >> use [x, h i, fxeq],
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es inyectiva e I no vacío, entonces
--    (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i)
-- ----------------------------------------------------------------------

example 
  (i : I) 
  (injf : injective f) 
  : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
begin
  intro y, 
  simp,
  intro h,
  rcases h i with ⟨x, xAi, fxeq⟩,
  use x, 
  split,
  { intro i',
    rcases h i' with ⟨x', x'Ai, fx'eq⟩,
    have : f x = f x', by rw [fxeq, fx'eq],
    have : x = x', from injf this,
    rw this,
    exact x'Ai },
  { exact fxeq },
end

-- Prueba
-- ======

/-
α : Type u1,
β : Type u2,
I : Type u3,
f : α → β,
A : I → set α,
i : I,
injf : injective f
⊢ (⋂ (i : I), f '' A i) ⊆ f '' ⋂ (i : I), A i
  >> intro y, 
y : β
⊢ (y ∈ ⋂ (i : I), f '' A i) → (y ∈ f '' ⋂ (i : I), A i)
  >> simp,
⊢ (∀ (i : I), ∃ (x : α), x ∈ A i ∧ f x = y) → 
  (∃ (x : α), (∀ (i : I), x ∈ A i) ∧ f x = y)
  >> intro h,
h : ∀ (i : I), ∃ (x : α), x ∈ A i ∧ f x = y
⊢ ∃ (x : α), (∀ (i : I), x ∈ A i) ∧ f x = y
  >> rcases h i with ⟨x, xAi, fxeq⟩,
x : α,
xAi : x ∈ A i,
fxeq : f x = y
⊢ ∃ (x : α), (∀ (i : I), x ∈ A i) ∧ f x = y
  >> use x, 
⊢ (∀ (i : I), x ∈ A i) ∧ f x = y
  >> split,
| ⊢ ∀ (i : I), x ∈ A i
|   >> { intro i',
| i' : I
| ⊢ x ∈ A i'
|   >>   rcases h i' with ⟨x', x'Ai, fx'eq⟩,
| i' : I,
| x' : α,
| x'Ai : x' ∈ A i',
| fx'eq : f x' = y
| ⊢ x ∈ A i'
|   >>   have : f x = f x', by rw [fxeq, fx'eq],
| this : f x = f x'
| ⊢ x ∈ A i'
|   >>   have : x = x', from injf this,
| this : x = x'
| ⊢ x ∈ A i'
|   >>   rw this,
| ⊢ x' ∈ A i'
|   >>   exact x'Ai },
⊢ f x = y
  >> { exact fxeq },
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i)
-- ----------------------------------------------------------------------

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by { ext x, simp }

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i)
-- ----------------------------------------------------------------------


example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by { ext x, simp }
