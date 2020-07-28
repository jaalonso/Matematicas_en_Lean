import tactic

open set

variable {α : Type*}
variables (s t u : set α)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    s ∩ (s ∪ t) = s
-- ----------------------------------------------------------------------

example : s ∩ (s ∪ t) = s :=
begin
  apply subset.antisymm,
  { rintros x ⟨xs,_⟩,
    exact xs },
  { rintros x xs,
    split,
    { exact xs },
    { apply mem_union_left,
      exact xs }},
end

-- Prueba
-- ======

/-
α : Type u_1,
s t : set α
⊢ s ∩ (s ∪ t) = s
  >> apply subset.antisymm,
| ⊢ s ∩ (s ∪ t) ⊆ s
|   >> { rintros x ⟨xs,_⟩,
| x : α,
| xs : x ∈ s,
| a_right : x ∈ s ∪ t
| ⊢ x ∈ s
|   >>   exact xs },
⊢ s ⊆ s ∩ (s ∪ t)
  >> { rintros x xs
x : α,
xs : x ∈ s
⊢ x ∈ s ∩ (s ∪ t),
  >>   split,
| ⊢ x ∈ s
|   >>   { exact xs },
⊢ x ∈ s ∪ t
  >>   { apply mem_union_left,
⊢ x ∈ s
  >>     exact xs }},
no goals
-/


example : s ∪ (s ∩ t) = s :=
sorry

example : (s \ t) ∪ t = s ∪ t :=
sorry

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
sorry
