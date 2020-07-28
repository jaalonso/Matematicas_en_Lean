import tactic

variable {α : Type*}
variables (s t u : set α)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u)
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  intros x hx,
  have xs : x ∈ s := hx.1,
  have xtu : x ∈ t ∪ u := hx.2,
  cases xtu with xt xu,
  { left,
    show x ∈ s ∩ t,
    exact ⟨xs, xt⟩ },
  { right,
    show x ∈ s ∩ u,
    exact ⟨xs, xu⟩ },
end

-- Prueba
-- ======

/-
α : Type u_1,
s t u : set α
⊢ s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u
  >> intros x hx,
x : α,
hx : x ∈ s ∩ (t ∪ u)
⊢ x ∈ s ∩ t ∪ s ∩ u
  >> have xs : x ∈ s := hx.1,
xs : x ∈ s
⊢ x ∈ s ∩ t ∪ s ∩ u
  >> have xtu : x ∈ t ∪ u := hx.2,
⊢ xtu : x ∈ t ∪ u
  >> cases xtu with xt xu,
| xt : x ∈ t
| ⊢ x ∈ s ∩ t ∪ s ∩ u
|   >> { left,
| ⊢ x ∈ s ∩ t
|   >>   show x ∈ s ∩ t,
| ⊢ x ∈ s ∩ t
|   >>   exact ⟨xs, xt⟩ },
xu : x ∈ u
⊢ x ∈ s ∩ t ∪ s ∩ u
  >> { right,
⊢ x ∈ s ∩ u
  >>   show x ∈ s ∩ u,
⊢ x ∈ s ∩ u
  >>   exact ⟨xs, xu⟩ },
no goals
-/

-- 2ª demostración
-- ===============

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  rintros x ⟨xs, xt | xu⟩,
  { left, 
    exact ⟨xs, xt⟩ },
  { right, 
    exact ⟨xs, xu⟩ },
end

-- Prueba
-- ======

/-
α : Type u_1,
s t u : set α
⊢ s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u
  >> rintros x ⟨xs, xt | xu⟩,
| x : α,
| xs : x ∈ s,
| xt : x ∈ t
| ⊢ x ∈ s ∩ t ∪ s ∩ u
|   >> { left, 
| ⊢ x ∈ s ∩ t
|   >>   exact ⟨xs, xt⟩ },
xu : x ∈ u
⊢ x ∈ s ∩ t ∪ s ∩ u
  >> { right, 
⊢ x ∈ s ∩ u
  >>   exact ⟨xs, xu⟩ },
no goals
-/

-- 3ª demostración
-- ===============

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
 rw set.inter_distrib_left,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)
-- ----------------------------------------------------------------------


example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) :=
begin
  rintros x (⟨xs,xt⟩ | ⟨xs,xu⟩),
  { split,
    { exact xs },
    { left,
      exact xt }},
  { split,
    { exact xs },
    { right,
      exact xu }},
end

-- Prueba
-- ======

/-
α : Type u_1,
s t u : set α
⊢ (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u)
  >> rintros x (⟨xs,xt⟩ | ⟨xs,xu⟩),
| x : α,
| xs : x ∈ s,
| xt : x ∈ t
| ⊢ x ∈ s ∩ (t ∪ u)
|   >> { split,
| | ⊢ x ∈ s
| |   >>   { exact xs },
| | ⊢ x ∈ t ∪ u
| |   >>   { left,
| | ⊢ x ∈ t
| |   >>     exact xt }},
x : α,
xs : x ∈ s,
xu : x ∈ u
⊢ x ∈ s ∩ (t ∪ u)
  >> { split,
| ⊢ x ∈ s
|   >>   { exact xs },
⊢ x ∈ t ∪ u
  >>   { right,
⊢ x ∈ u
  >>     exact xu }},
no goals
-/

