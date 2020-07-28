-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (s \ t) \ u ⊆ s \ (t ∪ u)
-- ----------------------------------------------------------------------

import tactic

variable {α : Type*}
variables (s t u : set α)

-- 1ª demostración
-- ===============

example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
begin
  intros x xstu,
  have xs : x ∈ s := xstu.1.1,
  have xnt : x ∉ t := xstu.1.2,
  have xnu : x ∉ u := xstu.2,
  split,
  { exact xs }, 
  { dsimp,
    intro xtu, 
    cases xtu with xt xu,
    { show false, 
      from xnt xt },
    { show false, 
      from xnu xu }},
end

-- Prueba
-- ======

/-
α : Type u_1,
s t u : set α
⊢ s \ t \ u ⊆ s \ (t ∪ u)
  >> intros x xstu,
x : α,
xstu : x ∈ s \ t \ u
⊢ x ∈ s \ (t ∪ u)
  >> have xs : x ∈ s := xstu.1.1,
xs : x ∈ s
⊢ x ∈ s \ (t ∪ u)
  >> have xnt : x ∉ t := xstu.1.2,
xnt : x ∉ t
⊢ x ∈ s \ (t ∪ u)
  >> have xnu : x ∉ u := xstu.2,
xnu : x ∉ u
⊢ x ∈ s \ (t ∪ u)
  >> split,
| ⊢ x ∈ s
|   >> { exact xs },
⊢ (λ (a : α), a ∉ t ∪ u) x 
  >> { dsimp,
⊢ ¬(x ∈ t ∨ x ∈ u)
  >>   intro xtu, 
xtu : x ∈ t ∨ x ∈ u
⊢ false
  >>   cases xtu with xt xu,
| xt : x ∈ t
| ⊢ false
|   >>   { show false, 
| ⊢ false
|   >>     from xnt xt },
xu : x ∈ u
⊢ false
  >>   { show false,
⊢ false 
  >>     from xnu xu }},
no goals
-/

-- 2ª demostración
-- ===============

example : s \ t \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨xs, xnt⟩, xnu⟩,
  use xs,
  rintros (xt | xu), 
  { contradiction },
  { contradiction },
end

-- Prueba
-- ======

/-
α : Type u_1,
s t u : set α
⊢ s \ t \ u ⊆ s \ (t ∪ u)
  >> rintros x ⟨⟨xs, xnt⟩, xnu⟩,
x : α,
xnu : x ∉ u,
xs : x ∈ s,
xnt : x ∉ t
⊢ x ∈ s \ (t ∪ u)
  >> use xs,
⊢ (λ (a : α), a ∉ t ∪ u) x
  >> rintros (xt | xu), 
| xt : x ∈ t
| ⊢ false
|   >> { contradiction },
xu : x ∈ u
⊢ false
  >> { contradiction },
no goals
-/



-- 3ª demostración
-- ===============

example : s \ t \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨xs, xnt⟩, xnu⟩,
  use xs,
  rintros (xt | xu); contradiction
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    s \ (t ∪ u) ⊆ (s \ t) \ u
-- ----------------------------------------------------------------------

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
begin
  rintros x ⟨xs, xntu⟩,
  use xs,
  { intro xt, 
    exact xntu (or.inl xt) },
  { intro xu,
    apply xntu (or.inr xu) },
end

-- Prueba
-- ======

/-
α : Type u_1,
s t u : set α
⊢ s \ (t ∪ u) ⊆ s \ t \ u
  >> rintros x ⟨xs, xntu⟩,
x : α,
xs : x ∈ s,
xntu : x ∉ t ∪ u
⊢ x ∈ s \ t \ u
  >> use xs,
| ⊢ (λ (a : α), a ∉ t) x
|   >> { intro xt, 
| xt : x ∈ t
| ⊢ false
|   >>   exact xntu (or.inl xt) },
⊢ (λ (a : α), a ∉ u) x
  >> { intro xu,
xu : x ∈ u
⊢ false
  >>   apply xntu (or.inr xu) },
no goals
-/

