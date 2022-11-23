-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la composición de funciones inyectivas es
-- inyectiva.
-- ----------------------------------------------------------------------

import tactic

open function

variables {α : Type*} {β : Type*} {γ : Type*}
variables {f : α → β} {g : β → γ}

-- 1ª demostración
-- ===============

example
  (hg : injective g)
  (hf : injective f) :
  injective (g ∘ f) :=
begin
  assume x : α,
  assume y : α,
  assume h1: (g ∘ f) x = (g ∘ f) y,
  have h2: g (f x) = g (f y) := h1,
  have h3: f x = f y := hg h2,
  show x = y,
    by exact hf h3,
end

-- 2ª demostración
-- ===============

example
  (hg : injective g)
  (hf : injective f) :
  injective (g ∘ f) :=
begin
  intros x y h,
  apply hf,
  apply hg,
  apply h,
end

-- Su desarrollo es
--
-- α : Type u_1,
-- β : Type u_2,
-- γ : Type u_3,
-- f : α → β,
-- g : β → γ,
-- hg : injective g,
-- hf : injective f
-- ⊢ injective (λ (x : α), g (f x))
--    >> intros x y h,
-- x y : α,
-- h : (λ (x : α), g (f x)) x = (λ (x : α), g (f x)) y
-- ⊢ x = y
--    >> apply hf,
-- ⊢ f x = f y
--    >> apply hg,
-- ⊢ g (f x) = g (f y)
--    >> apply h,
-- no goals

-- 3ª demostración
-- ===============

example
  (hg : injective g)
  (hf : injective f) :
  injective (g ∘ f) :=
λ x y h, hf (hg h)

-- 4ª demostración
-- ===============

example
  (hg : injective g)
  (hf : injective f) :
  injective (g ∘ f) :=
-- by library_search
injective.comp hg hf

-- 5ª demostración
-- ===============

example
  (hg : injective g)
  (hf : injective f) :
  injective (g ∘ f) :=
-- by hint
by tauto
