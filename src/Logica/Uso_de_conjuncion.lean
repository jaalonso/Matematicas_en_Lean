-- ---------------------------------------------------------------------
-- Ejercicio. Sean m y n números naturales. Demostrar que si
--    m ∣ n ∧ m ≠ n
-- entonces
--    m ∣ n ∧ ¬ n ∣ m
-- ----------------------------------------------------------------------

import data.nat.gcd

open nat

variables {m n : ℕ} 

-- 1ª demostración
-- ===============

example 
  (h : m ∣ n ∧ m ≠ n) 
  : m ∣ n ∧ ¬ n ∣ m :=
begin
  cases h with h₀ h₁,
  split,
    exact h₀,
  contrapose! h₁,
  apply dvd_antisymm h₀ h₁,
end

-- Prueba
-- ======

/-
m n : ℕ,
h : m ∣ n ∧ m ≠ n
⊢ m ∣ n ∧ ¬n ∣ m
  >> cases h with h₀ h₁,
h₀ : m ∣ n,
h₁ : m ≠ n
⊢ m ∣ n ∧ ¬n ∣ m
  >> split,
| ⊢ m ∣ n
|   >>   exact h₀,
⊢ ¬n ∣ m
  >> contrapose! h₁,
h₁ : n ∣ m
⊢ m = n
  >> apply dvd_antisymm h₀ h₁,
no goals
-/

-- 2ª demostración
-- ===============

example 
  (h : m ∣ n ∧ m ≠ n) 
  : m ∣ n ∧ ¬ n ∣ m :=
begin
  rcases h with ⟨h₀, h₁⟩,
  split,
    exact h₀,
  contrapose! h₁,
  apply dvd_antisymm h₀ h₁,
end

-- Prueba
-- ======

/-
m n : ℕ,
h : m ∣ n ∧ m ≠ n
⊢ m ∣ n ∧ ¬n ∣ m
  >> rcases h with ⟨h₀, h₁⟩,
h₀ : m ∣ n,
h₁ : m ≠ n
⊢ m ∣ n ∧ ¬n ∣ m
  >> split,
| ⊢ m ∣ n
|   >>   exact h₀,
⊢ ¬n ∣ m
  >> contrapose! h₁,
h₁ : n ∣ m
⊢ m = n
  >> apply dvd_antisymm h₀ h₁,
no goals
-/

