import data.set.function

open set

universes u v
variable {α : Type u}
variable {β : Type v}
variable (f : α → β)
variable (s : set α)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que f es inyectiva sobre s syss
--    ∀ {x₁ x₂}, x₁ ∈ s → x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂
-- ----------------------------------------------------------------------

example :
  inj_on f s ↔
  ∀ ⦃x₁ : α⦄, x₁ ∈ s → ∀ ⦃x₂ : α⦄, x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂ :=
iff.rfl
