-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que en los reales, si
--    x ≤ y ∧ x ≠ y
-- entonces
--    ¬ y ≤ x 
-- ----------------------------------------------------------------------

import data.real.basic

variables {x y : ℝ} 

-- 1ª demostración
-- ===============

example 
  (h : x ≤ y ∧ x ≠ y) 
  : ¬ y ≤ x :=
begin
  cases h with h₀ h₁,
  contrapose! h₁,
  exact le_antisymm h₀ h₁,
end

-- Prueba
-- ======

/-
x y : ℝ,
h : x ≤ y ∧ x ≠ y
⊢ ¬y ≤ x
  >> cases h with h₀ h₁,
h₀ : x ≤ y,
h₁ : x ≠ y
⊢ ¬y ≤ x
  >> contrapose! h₁,
h₀ : x ≤ y,
h₁ : y ≤ x
⊢ x = y
  >> exact le_antisymm h₀ h₁, 
no goals
-/


-- Comentario: La táctica (cases h with h₀ h₁,) si la hipótesis h es una
-- conjunción (P ∧ Q), aplica la regla de eliminación de la conjunción;
-- es decir, sustituy h por las hipótesis (h₀ : P) y (h₁ : Q).

-- 2ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
begin
  rintros ⟨h₀, h₁⟩ h',
  exact h₁ (le_antisymm h₀ h'),
end

-- Prueba
-- ======

/-
x y : ℝ
⊢ x ≤ y ∧ x ≠ y → ¬y ≤ x
  >> rintros ⟨h₀, h₁⟩ h',
h' : y ≤ x,
h₀ : x ≤ y,
h₁ : x ≠ y
⊢ false
  >> exact h₁ (le_antisymm h₀ h'),
no goals
-/

-- Comentario: La táctica (rintros ⟨h₀, h₁⟩ h') 
-- + si el objetivo es de la forma (P ∧ Q → (R → S)) añade las hipótesis 
--   (h₀ : P), (h₁ : Q), (h' : R) y sustituye el objetivo por S.
-- + si el objetivo es de la forma (P ∧ Q → ¬R) añade las hipótesis 
--   (h₀ : P), (h₁ : Q), (h' : R) y sustituye el objetivo por false.

-- 3ª demostración
-- ===============

example : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
λ ⟨h₀, h₁⟩ h', h₁ (le_antisymm h₀ h')

-- 4ª demostración
-- ===============

example 
  (h : x ≤ y ∧ x ≠ y) 
  : ¬ y ≤ x :=
begin
  intro h',
  apply h.right,
  exact le_antisymm h.left h',
end

-- Prueba
-- ======

/-
x y : ℝ,
h : x ≤ y ∧ x ≠ y
⊢ ¬y ≤ x
  >> intro h',
h' : y ≤ x
⊢ false
  >> apply h.right,
h' : y ≤ x
⊢ x = y
  >> exact le_antisymm h.left h',
no goals
-/

-- Comentario: Si h es una conjunción (P ∧ Q), entonces h.left es P y
-- h.right es Q. 

-- 5ª demostración
-- ===============

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
λ h', h.right (le_antisymm h.left h')
