-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--     converges_to (ℕ → ℝ) → ℝ → Prop
-- tal que (converges_to s a) afirma que a es el límite de s.
-- ----------------------------------------------------------------------

import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

-- #print converges_to

-- Comentario: Al colocar el cursor sobre print se obtiene
--    def converges_to : (ℕ → ℝ) → ℝ → Prop :=
--    λ (s : ℕ → ℝ) (a : ℝ),
--      ∀ (ε : ℝ), ε > 0 → (∃ (N : ℕ), ∀ (n : ℕ),
--        n ≥ N → abs (s n - a) < ε)
