-- Teorema_de_Cantor.lean
-- Teorema de Cantor
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 4-mayo-2022
-- ---------------------------------------------------------------------

import data.set.basic
import set_theory.cardinal

open set

-- 1ª demostración
-- ===============

theorem cantor_injective
  {α : Type} (f : set α → α) :
  ¬function.injective f :=
begin
  set B := {x : set α | f x ∉ x},
  set B' := {y : α | ∃ x : set α, f x = y ∧ x ∈ B},
  by_contradiction h,
  by_cases hp : f(B') ∈ B',
  { have : ∃ X, f(X) = f(B') ∧ f(X) ∉ X := mem_set_of_eq.mp hp,
    cases this with s hs,
    rw ← (h hs.1) at hp,
    have hp' := hs.2,
    contradiction, },
  { have : f(B') ∈ B',
    { rw mem_set_of_eq,
      use B',
      split,
      { refl, },
      { rw mem_set_of_eq,
        exact hp, }, },
    contradiction, },
end

-- 2ª demostración
-- ===============

theorem cantor_injective2
  {α : Type}
  (f : set α → α)
  : ¬function.injective f :=
begin
  set B := {x : set α | f x ∉ x},
  set B' := {y : α | ∃ x : set α, f x = y ∧ x ∈ B},
  intro h,
  by_cases hp : f B' ∈ B',
  { obtain ⟨s, hs⟩ : ∃ X, f X = f B' ∧ f X ∉ X := set.mem_set_of_eq.mp hp,
    rw ← (h hs.1) at hp,
    exact hs.2 hp, },
  { exact hp ⟨B', rfl, hp⟩, }
end

-- 2ª teorema
-- ==========

theorem cantor_surjective'
  {α : Type}
  (f : α → set α)
  : ¬function.surjective f :=
begin
  set B := {x : α | x ∉ f x},
  by_contradiction,
  obtain ⟨ξ, fx⟩ : ∃ ξ, f ξ = B := h B,
  have : ξ ∈ B ↔ ξ ∉ f(ξ),
  { exact mem_def, },
  { rw fx at this,
    exact (iff_not_self (ξ ∈ B)).mp this, },
end
