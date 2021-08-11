-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones
-- 1. Importar la librería tactic
-- 2. Abrir el espacio de nombres set
-- 3. Declarar u y v como variables de universos.
-- 4. Declarar α como una variable de tipos en u.
-- 5. Declarar I como una variable de tipos en v.
-- 6. Declarar A y B como variables sobre funciones de I en α.
-- 7. Declarar s como variable sobre conjuntos de elementos de α.
-- ----------------------------------------------------------------------

import tactic                 -- 1
open set                      -- 2
universes u v                 -- 3
variable (α : Type u)         -- 4
variable (I : Type v)         -- 5
variables (A B : I → set α)   -- 6
variable  s : set α           -- 7

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s)
-- ----------------------------------------------------------------------

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Union],
  split,
  { rintros ⟨xs, ⟨i, xAi⟩⟩,
    exact ⟨i, xAi, xs⟩ },
  { rintros ⟨i, xAi, xs⟩,
    exact ⟨xs, ⟨i, xAi⟩⟩ },
end

-- Prueba
-- ======

/-
α : Type u,
I : Type v,
A : I → set α,
s : set α
⊢ (s ∩ ⋃ (i : I), A i) = ⋃ (i : I), A i ∩ s
  >> ext x,
x : α
⊢ (x ∈ s ∩ ⋃ (i : I), A i) ↔ x ∈ ⋃ (i : I), A i ∩ s
  >> simp only [mem_inter_eq, mem_Union],
⊢ (x ∈ s ∧ ∃ (i : I), x ∈ A i) ↔ ∃ (i : I), x ∈ A i ∧ x ∈ s
  >> split,
| ⊢ (x ∈ s ∧ ∃ (i : I), x ∈ A i) → (∃ (i : I), x ∈ A i ∧ x ∈ s)
|   >> { rintros ⟨xs, ⟨i, xAi⟩⟩,
| x : α,
| xs : x ∈ s,
| i : I,
| xAi : x ∈ A i
| ⊢ ∃ (i : I), x ∈ A i ∧ x ∈ s
|   >>   exact ⟨i, xAi, xs⟩ },
⊢ (∃ (i : I), x ∈ A i ∧ x ∈ s) → (x ∈ s ∧ ∃ (i : I), x ∈ A i)
  >> { rintros ⟨i, xAi, xs⟩,
x : α,
i : I,
xAi : x ∈ A i,
xs : x ∈ s
⊢ x ∈ s ∧ ∃ (i : I), x ∈ A i
  >>   exact ⟨xs, ⟨i, xAi⟩⟩ },
no goals
-/

-- Comentario: Se han usado los lemas
-- + mem_inter_eq: x ∈ a ∩ b = (x ∈ a ∧ x ∈ b)
-- + mem_Union : x ∈ Union A ↔ ∃ (i : I), x ∈ A i

-- Comprobación
variable x : α
variables (a b : set α)
-- #check @mem_inter_eq _ x a b
-- #check @mem_Union α I x A

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i)
-- ----------------------------------------------------------------------

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Inter],
  split,
  { intro h,
    split,
    { intro i,
      exact (h i).1 },
    { intro i,
      exact (h i).2 }},
  { rintros ⟨h1, h2⟩ i,
    split,
    { exact h1 i },
    { exact h2 i }},
end

-- Prueba
-- ======

/-
α : Type u,
I : Type v,
A B : I → set α
⊢ (⋂ (i : I), A i ∩ B i) = (⋂ (i : I), A i) ∩ ⋂ (i : I), B i
  >> ext x,
x : α
⊢ (x ∈ ⋂ (i : I), A i ∩ B i) ↔ x ∈ (⋂ (i : I), A i) ∩ ⋂ (i : I), B i
  >> simp only [mem_inter_eq, mem_Inter],
⊢ (∀ (i : I), x ∈ A i ∧ x ∈ B i) ↔ (∀ (i : I), x ∈ A i) ∧ ∀ (i : I), x ∈ B i
  >> split,
| ⊢ (∀ (i : I), x ∈ A i ∧ x ∈ B i) → ((∀ (i : I), x ∈ A i) ∧ ∀ (i : I), x ∈ B i)
|   >> { intro h,
| h : ∀ (i : I), x ∈ A i ∧ x ∈ B i
| ⊢ (∀ (i : I), x ∈ A i) ∧ ∀ (i : I), x ∈ B i
|   >>   split,
| | ⊢ ∀ (i : I), x ∈ A i
| |   >>   { intro i,
| | i : I
| | ⊢ x ∈ A i
| |   >>     exact (h i).1 },
| ⊢ ∀ (i : I), x ∈ B i
|   >>   { intro i,
| i : I
| ⊢ x ∈ B i
|   >>     exact (h i).2 }},
⊢ ((∀ (i : I), x ∈ A i) ∧ ∀ (i : I), x ∈ B i) → ∀ (i : I), x ∈ A i ∧ x ∈ B i
  >> { rintros ⟨h1, h2⟩ i,
i : I,
h1 : ∀ (i : I), x ∈ A i,
h2 : ∀ (i : I), x ∈ B i
⊢ x ∈ A i ∧ x ∈ B i
  >>   split,
| ⊢ x ∈ A i
|   >>   { exact h1 i },
⊢ x ∈ B i
  >>   { exact h2 i }},
no goals
-/

-- Comentario: Se han usado los lemas
-- + mem_inter_eq: x ∈ a ∩ b = (x ∈ a ∧ x ∈ b)
-- + mem_Inter : x ∈ Inter A ↔ ∀ (i : I), x ∈ A i

-- Comprobación
-- #check @mem_inter_eq _ x a b
-- #check @mem_Inter α I x A
