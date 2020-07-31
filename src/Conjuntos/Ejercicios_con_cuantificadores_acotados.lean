-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones:
-- 1. Importar la librería data.nat.prime data.nat.parity
-- 2. Abrir el espacio de nombres nat
-- 3. Declarar s y t como variables sobre conjuntos de números naturales.
-- 4. Declarar el hecho (ssubt : s ⊆ t)
-- 5, Añadir ssubt como hipótesis de la teoría.
-- ----------------------------------------------------------------------

import data.nat.prime data.nat.parity  -- 1
open nat                               -- 2
variables (s t : set ℕ)                -- 3
variables (ssubt : s ⊆ t)              -- 4
include ssubt                          -- 5

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    ∀ x ∈ t, ¬ even x
--    ∀ x ∈ t, prime x
-- entonces
--    ∀ x ∈ s, ¬ even x ∧ prime x
-- ----------------------------------------------------------------------

example 
  (h₀ : ∀ x ∈ t, ¬ even x) 
  (h₁ : ∀ x ∈ t, prime x) 
  : ∀ x ∈ s, ¬ even x ∧ prime x :=
begin
  intros x xs,
  split,
  { apply h₀ x (ssubt xs) },
  { apply h₁ x (ssubt xs) },
end

-- Prueba
-- ======

/-
s t : set ℕ,
ssubt : s ⊆ t,
h₀ : ∀ (x : ℕ), x ∈ t → ¬x.even,
h₁ : ∀ (x : ℕ), x ∈ t → x.prime
⊢ ∀ (x : ℕ), x ∈ s → ¬x.even ∧ x.prime
  >> intros x xs,
x : ℕ,
xs : x ∈ s
⊢ ¬x.even ∧ x.prime
  >> split,
| ⊢ ¬x.even
|   >> { apply h₀ x (ssubt xs) },
⊢ x.prime
  >> { apply h₁ x (ssubt xs) },
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    ∃ x ∈ s, ¬ even x ∧ prime x
-- entonces
--   ∃ x ∈ t, prime x 
-- ----------------------------------------------------------------------

example 
  (h : ∃ x ∈ s, ¬ even x ∧ prime x) 
  : ∃ x ∈ t, prime x :=
begin
  rcases h with ⟨x, xs, _, px⟩,
  use [x, ssubt xs, px],
end

-- Prueba
-- ======

/-
s t : set ℕ,
ssubt : s ⊆ t,
h : ∃ (x : ℕ) (H : x ∈ s), ¬x.even ∧ x.prime
⊢ ∃ (x : ℕ) (H : x ∈ t), x.prime
  >> rcases h with ⟨x, xs, _, px⟩,
x : ℕ,
xs : x ∈ s,
h_h_h_left : ¬x.even,
px : x.prime
⊢ ∃ (x : ℕ) (H : x ∈ t), x.prime
  >> use [x, ssubt xs, px],
no goals
-/

