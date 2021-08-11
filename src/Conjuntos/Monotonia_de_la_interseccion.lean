-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar si
--    s ⊆ t
-- entonces
--    s ∩ u ⊆ t ∩ u
-- ----------------------------------------------------------------------

import tactic

variable {α : Type*}
variables (s t u : set α)

open set

-- 1ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  rw subset_def,
  rw inter_def,
  rw inter_def,
  dsimp,
  rw subset_def at h,
  rintros x ⟨xs, xu⟩,
  split,
  { exact h x xs },
  { exact xu },
end

-- Prueba
-- ======

/-
α : Type u_1,
s t u : set α,
h : s ⊆ t
⊢ s ∩ u ⊆ t ∩ u
  >> rw subset_def,
⊢ ∀ (x : α), x ∈ s ∩ u → x ∈ t ∩ u
  >> rw inter_def,
⊢ ∀ (x : α), x ∈ {a : α | a ∈ s ∧ a ∈ u} → x ∈ t ∩ u
  >> rw inter_def,
⊢ ∀ (x : α), x ∈ {a : α | a ∈ s ∧ a ∈ u} → x ∈ {a : α | a ∈ t ∧ a ∈ u}
  >> dsimp,
⊢ ∀ (x : α), x ∈ s ∧ x ∈ u → x ∈ t ∧ x ∈ u
  >> rw subset_def at h,
h : ∀ (x : α), x ∈ s → x ∈ t
⊢ ∀ (x : α), x ∈ s ∧ x ∈ u → x ∈ t ∧ x ∈ u
  >> rintros x ⟨xs, xu⟩,
x : α,
xs : x ∈ s,
xu : x ∈ u
⊢ x ∈ t ∧ x ∈ u
  >> split,
| ⊢ x ∈ t
|   >> { exact h x xs },
⊢ x ∈ u
  >> { exact xu },
no goals
-/

-- 2ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  rw [subset_def, inter_def, inter_def],
  dsimp,
  rw subset_def at h,
  rintros x ⟨xs, xu⟩,
  exact ⟨h _ xs, xu⟩,
end

-- Prueba
-- ======

/-
α : Type u_1,
s t u : set α,
h : s ⊆ t
⊢ s ∩ u ⊆ t ∩ u  >> rw [subset_def, inter_def, inter_def],
  >> dsimp,
⊢ ∀ (x : α), x ∈ s ∧ x ∈ u → x ∈ t ∧ x ∈ u
  >> rw subset_def at h,
h : ∀ (x : α), x ∈ s → x ∈ t
⊢ ∀ (x : α), x ∈ s ∧ x ∈ u → x ∈ t ∧ x ∈ u
  >> rintros x ⟨xs, xu⟩,
x : α,
xs : x ∈ s,
xu : x ∈ u
⊢ x ∈ t ∧ x ∈ u
  >> exact ⟨h _ xs, xu⟩,
no goals
-/

-- 3ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  simp only [subset_def, mem_inter_eq] at *,
  rintros x ⟨xs, xu⟩,
  exact ⟨h _ xs, xu⟩,
end

-- Prueba
-- ======

/-
α : Type u_1,
s t u : set α,
h : s ⊆ t
⊢ s ∩ u ⊆ t ∩ u
  >> simp only [subset_def, mem_inter_eq] at *,
h : ∀ (x : α), x ∈ s → x ∈ t
⊢ ∀ (x : α), x ∈ s ∧ x ∈ u → x ∈ t ∧ x ∈ u
  >> rintros x ⟨xs, xu⟩,
x : α,
xs : x ∈ s,
xu : x ∈ u
⊢ x ∈ t ∧ x ∈ u
  >> exact ⟨h _ xs, xu⟩,
no goals
-/

-- 4ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
by finish [subset_def, mem_inter_eq]

-- 5ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
begin
  intros x xsu,
  exact ⟨h xsu.1, xsu.2⟩,
end

-- Prueba
-- ======

/-
α : Type u_1,
s t u : set α,
h : s ⊆ t
⊢ s ∩ u ⊆ t ∩ u
  >> intros x xsu,
x : α,
xsu : x ∈ s ∩ u
⊢ x ∈ t ∩ u
  >> exact ⟨h xsu.1, xsu.2⟩,
no goals
-/

-- Comentario: La táctica *intro* aplica una *reducción definicional*
-- expandiendo las definiciones.

-- 6ª demostración
-- ===============

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
by exact λ x ⟨xs, xu⟩, ⟨h xs, xu⟩

-- 7ª demostración
-- ===============

lemma monotonia
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
λ x ⟨xs, xu⟩, ⟨h xs, xu⟩

-- 8ª demostración
-- ===============

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
inter_subset_inter_left u h

-- Comentario: Se han usado los lemas
-- + inter_def : s ∩ t = {a : α | a ∈ s ∧ a ∈ t}
-- + inter_subset_inter_left : s ⊆ t → s ∩ u ⊆ t ∩ u
-- + mem_inter_eq x s t : x ∈ s ∩ t = (x ∈ s ∧ x ∈ t)
-- + subset_def : s ⊆ t = ∀ (x : α), x ∈ s → x ∈ t

-- Comprobación:
variable (x : α)
-- #check @subset_def _ s t
-- #check @inter_def _ s t
-- #check @mem_inter_eq _ x s t
-- #check @inter_subset_inter_left _ s t u
