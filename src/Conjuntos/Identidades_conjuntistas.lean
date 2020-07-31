-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    s ∩ (s ∪ t) = s
-- ----------------------------------------------------------------------

import tactic

open set

variable {α : Type*}
variables (s t u : set α)

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

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    s ∪ (s ∩ t) = s
-- ----------------------------------------------------------------------

example : s ∪ (s ∩ t) = s :=
begin
  apply subset.antisymm,
  { rintros x (xs | ⟨xs,xt⟩),
    { exact xs },
    { exact xs }},
  { rintros x xs,
    left,
    exact xs },
end

-- Prueba
-- ======

/-
α : Type u_1,
s t : set α
⊢ s ∪ s ∩ t = s
  >> apply subset.antisymm,
| ⊢ s ∪ s ∩ t ⊆ s
|   >> { rintros x (xs | ⟨xs,xt⟩),
| | x : α,
| | xs : x ∈ s
| | ⊢ x ∈ s
| |  >>   { exact xs },
| x : α,
| xs : x ∈ s,
| xt : x ∈ t
| ⊢ x ∈ s
|   >>   { exact xs }},
⊢ s ⊆ s ∪ s ∩ t
  >> { rintros x xs,
x : α,
xs : x ∈ s
⊢ x ∈ s ∪ s ∩ t
  >>   left,
⊢ x ∈ s
  >>   exact xs },
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (s \ t) ∪ t = s ∪ t
-- ----------------------------------------------------------------------


example : (s \ t) ∪ t = s ∪ t :=
begin
  ext x, 
  split,
  { rintros (⟨xs, xnt⟩ | xt),
    { left, 
      exact xs },
    { right, 
    exact xt }},
  rintros (xs | xt),
  { classical,
    by_cases xt : x ∈ t,
    { right, 
      exact xt },
    { left, 
      exact ⟨xs, xt⟩ }},
  { right, 
    exact xt },

end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t)
-- ----------------------------------------------------------------------

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  apply  subset.antisymm,
  { rintros x (⟨xs,xnt⟩ | ⟨xt,xns⟩),
    { split,
      { exact mem_union_left t xs },
      { intro h,
        apply xnt,
        exact mem_of_mem_inter_right h }},
    { split,
      { exact mem_union_right s xt },
      { intro h,
        apply xns,
        exact mem_of_mem_inter_left h }}},
  { rintros x ⟨xs | xt,xnst⟩,
    { left,
      split,
      { exact xs },
      { intro h,
        apply xnst,
        exact mem_sep xs h }},
    { right,
      split, 
      { exact xt },
      { intro h,
        apply xnst,
        exact mem_sep h xt }}},
end

-- Prueba
-- ======

/-
α : Type u_1,
s t : set α
⊢ s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t)
  apply  subset.antisymm,
| ⊢ s \ t ∪ t \ s ⊆ (s ∪ t) \ (s ∩ t)
|   { rintros x (⟨xs,xnt⟩ | ⟨xt,xns⟩),
| | x : α,
| | xs : x ∈ s,
| | xnt : x ∉ t
| | ⊢ x ∈ (s ∪ t) \ (s ∩ t)
| |     { split,
| | | ⊢ x ∈ s ∪ t
| | |       { exact mem_union_left t xs },
| | ⊢ (λ (a : α), a ∉ s ∩ t) x
| |       { intro h,
| | h : x ∈ s ∩ t
| | ⊢ false
| |         apply xnt,
| | ⊢ x ∈ t
| |         exact mem_of_mem_inter_right h }},
| x : α,
| xt : x ∈ t,
| xns : x ∉ s
| ⊢ x ∈ (s ∪ t) \ (s ∩ t)
|     { split,
| | ⊢ x ∈ s ∪ t
| |       { exact mem_union_right s xt },
| ⊢ (λ (a : α), a ∉ s ∩ t) x
|       { intro h,
| h : x ∈ s ∩ t
| ⊢ false
|         apply xns,
| ⊢ x ∈ s
|         exact mem_of_mem_inter_left h }}},
⊢ (s ∪ t) \ (s ∩ t) ⊆ s \ t ∪ t \ s
  { rintros x ⟨xs | xt,xnst⟩,
| x : α,
| xnst : x ∉ s ∩ t,
| xs : x ∈ s
| ⊢ x ∈ s \ t ∪ t \ s
|     { left,
| ⊢ x ∈ s \ t
|       split,
| ⊢ x ∈ s
| |       { exact xs },
| ⊢ (λ (a : α), a ∉ t) x
|       { intro h,
| h : x ∈ t
| ⊢ false
|         apply xnst,
| ⊢ x ∈ s ∩ t
|         exact mem_sep xs h }},
⊢ x ∈ s \ t ∪ t \ s
    { right,
⊢ x ∈ t \ s
      split,
| ⊢ x ∈ t
|       { exact xt },
⊢ (λ (a : α), a ∉ s) x
      { intro h,
h : x ∈ s
⊢ false
        apply xnst,
⊢ x ∈ s ∩ t
        exact mem_sep h xt }}},
no goals
-/


#lint
