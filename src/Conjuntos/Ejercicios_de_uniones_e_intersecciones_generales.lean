-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones
-- 1. Importar la librería tactic
-- 2. Abrir el espacio de nombres set
-- 3. Declarar u y v como variables de universos.
-- 4. Declarar α como una variable de tipos en u.
-- 5. Declarar I como una variable de tipos en v.
-- 6. Declarar A y B como variables sobre funciones de I en α.
-- 7. Declarar s como variable sobre conjuntos de elementos de α. 
-- 8. Usar la lógica clásica.
-- ----------------------------------------------------------------------

import tactic                 -- 1
open set                      -- 2
universes u v                 -- 3
variable (α : Type u)         -- 4
variable (I : Type v)         -- 5
variables (A B : I → set α)   -- 6
variable  s : set α           -- 7
open_locale classical         -- 8

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s)
-- ----------------------------------------------------------------------

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin
  ext x,
  simp only [mem_union, mem_Inter],
  split,
  { rintros (xs | xI),
    { intro i, 
      right, 
      exact xs },
    { intro i, 
      left, 
      exact xI i }},
  { intro h,
    by_cases xs : x ∈ s,
    { left, 
      exact xs },
    { right,
      intro i,
      cases h i,
      { assumption },
      { contradiction }}},
end

-- Prueba
-- ======

/-
α : Type u,
I : Type v,
A : I → set α,
s : set α
⊢ (s ∪ ⋂ (i : I), A i) = ⋂ (i : I), A i ∪ s
  >> ext x,
x : α
⊢ (x ∈ s ∪ ⋂ (i : I), A i) ↔ x ∈ ⋂ (i : I), A i ∪ s
  >> simp only [mem_union, mem_Inter],
⊢ (x ∈ s ∨ ∀ (i : I), x ∈ A i) ↔ ∀ (i : I), x ∈ A i ∨ x ∈ s
  >> split,
| ⊢ (x ∈ s ∨ ∀ (i : I), x ∈ A i) → ∀ (i : I), x ∈ A i ∨ x ∈ s
|   >> { rintros (xs | xI),
| | xs : x ∈ s
| | ⊢ ∀ (i : I), x ∈ A i ∨ x ∈ s
| |   >>   { intro i,
| | i : I
| | ⊢ x ∈ A i ∨ x ∈ s 
| |   >>     right, 
| | ⊢ x ∈ s
| |   >>     exact xs },
| ⊢ ∀ (i : I), x ∈ A i ∨ x ∈ s
|   >>   { intro i, 
| i : I
| ⊢ x ∈ A i ∨ x ∈ s
|   >>     left, 
| ⊢ x ∈ A i
|   >>     exact xI i }},
⊢ (∀ (i : I), x ∈ A i ∨ x ∈ s) → (x ∈ s ∨ ∀ (i : I), x ∈ A i)
  >> { intro h,
h : ∀ (i : I), x ∈ A i ∨ x ∈ s
⊢ x ∈ s ∨ ∀ (i : I), x ∈ A i
  >>   by_cases xs : x ∈ s,
| xs : x ∈ s
| ⊢ x ∈ s ∨ ∀ (i : I), x ∈ A i
|   >>   { left, 
| ⊢ x ∈ s
|   >>     exact xs },
xs : x ∉ s
⊢ x ∈ s ∨ ∀ (i : I), x ∈ A i
  >>   { right,
⊢ ∀ (i : I), x ∈ A i
  >>     intro i,
i : I
⊢ x ∈ A i
  >>     cases h i,
| h_1 : x ∈ A i
| ⊢ x ∈ A i
|   >>     { assumption },
⊢ x ∈ A i
  >>     { contradiction }}},
no goals
-/


