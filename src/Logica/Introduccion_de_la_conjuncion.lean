-- ---------------------------------------------------------------------
-- Ejercicio. Sean x e y dos números tales que
--    x ≤ y 
--    ¬ y ≤ x
-- entonces 
--    x ≤ y ∧ x ≠ y
-- ----------------------------------------------------------------------

import data.real.basic

variables {x y : ℝ}

-- 1ª demostración
-- ===============
example  
  (h₀ : x ≤ y) 
  (h₁ : ¬ y ≤ x) 
  : x ≤ y ∧ x ≠ y :=
begin
  split,
  { assumption },
  intro h,
  apply h₁,
  rw h,
end

-- Prueba
-- ======

/-
x y : ℝ,
h₀ : x ≤ y,
h₁ : ¬y ≤ x
⊢ x ≤ y ∧ x ≠ y
  >> split,
| ⊢ x ≤ y
|   >> { assumption },
| ⊢ x ≠ y
|   >> intro h,
| h : x = y
| ⊢ false
|   >> apply h₁,
| ⊢ y ≤ x
|   >> rw h.
no goals
-/

-- Comentario: La táctica split, cuando el objetivo es una conjunción 
-- (P ∧ Q), aplica la regla de introducción de la conjunción; es decir,
-- sustituye el objetivo por dos nuevos subobjetivos (P y Q).

-- 2ª demostración
-- ===============

example 
  (h₀ : x ≤ y) 
  (h₁ : ¬ y ≤ x) 
  : x ≤ y ∧ x ≠ y :=
⟨h₀, λ h, h₁ (by rw h)⟩

-- Comentario: La notación ⟨h0, h1⟩, cuando el objetivo es una conjunción 
-- (P ∧ Q), aplica la regla de introducción de la conjunción donde h0 es
-- una prueba de P y h1 de Q.

-- 3ª demostración
-- ===============

example 
  (h₀ : x ≤ y) 
  (h₁ : ¬ y ≤ x) 
  : x ≤ y ∧ x ≠ y :=
begin
  have h : x ≠ y,
  { contrapose! h₁,
    rw h₁ },
  exact ⟨h₀, h⟩,
end

-- Prueba
-- ======

/-
x y : ℝ,
h₀ : x ≤ y,
h₁ : ¬y ≤ x
⊢ x ≤ y ∧ x ≠ y
  >> have h : x ≠ y,
  >> { contrapose! h₁,
h₁ : x = y
⊢ y ≤ x
  >>   rw h₁ },
h : x ≠ y
⊢ x ≤ y ∧ x ≠ y
  >> exact ⟨h₀, h⟩,
no goals
-/


