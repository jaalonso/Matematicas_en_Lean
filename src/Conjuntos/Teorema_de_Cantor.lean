-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar el teorema de Cantor: No existe singuna
-- aplicación suprayectiva de un conjunto en su conjunto potencia.  
-- ----------------------------------------------------------------------

import data.set.basic

open function

variable {α : Type*}

theorem Cantor : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := { i | i ∉ f i},
  rcases surjf S with j,
  have h₁ : j ∉ f j,
  { intro h',
    have : j ∉ f j,
      { by rwa h at h' },
    contradiction },
  have h₂ : j ∈ S,
    from h₁,
  have h₃ : j ∉ S,
    by rwa h at h₁,
  contradiction,
end

-- Prueba
-- ======

/-
α : Type u_1
⊢ ∀ (f : α → set α), ¬surjective f
  >> intros f surjf,
f : α → set α,
surjf : surjective f
⊢ false
  >> let S := { i | i ∉ f i},
S : set α := {i : α | i ∉ f i}
⊢ false
  >> rcases surjf S with j,
j : α,
h : f j = S
⊢ false
  >> have h₁ : j ∉ f j,
| ⊢ j ∉ f j
|   >> { intro h',
| h' : j ∈ f j
| ⊢ false
|   >>   have : j ∉ f j,
| | ⊢ j ∉ f j
| |   >>     { by rwa h at h' },
| this : j ∉ f j
| ⊢ false
|   >>   contradiction },
h₁ : j ∉ f j
⊢ false
  >> have h₂ : j ∈ S,
| ⊢ j ∈ S
|   >>   from h₁,
h₂ : j ∈ S
⊢ false
  >> have h₃ : j ∉ S,
  >>   by rwa h at h₁,
h₃ : j ∉ S
⊢ false
  >> contradiction,
no goals
-/

