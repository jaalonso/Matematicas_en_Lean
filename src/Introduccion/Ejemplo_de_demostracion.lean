-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que los productos de los números naturales por
-- números pares son pares.
-- ---------------------------------------------------------------------

import data.nat.parity
import tactic

open nat

-- 1ª demostración
example : ∀ m n : ℕ, even n → even (m * n) :=
  assume m n ⟨k, (hk : n = k + k)⟩,
  have hmn : m * n = m * k + m * k,
    by rw [hk, mul_add],
  show ∃ l, m * n = l + l,
    from ⟨_, hmn⟩

-- 2ª demostración (mediante término)
example : ∀ m n : ℕ, even n → even (m * n) :=
  λ m n ⟨k, hk⟩, ⟨m * k, by rw [hk, mul_add]⟩

-- 3ª demostración (mediante tácticas)
example : ∀ m n : ℕ, even n → even (m * n) :=
  begin
    rintros m n ⟨k, hk⟩,
    use m * k,
    rw [hk, mul_add]
  end

-- 4ª demostración (mediante tácticas en una línea)
example : ∀ m n : ℕ, even n → even (m * n) :=
  by rintros m n ⟨k, hk⟩; use m * k; rw [hk, mul_add]

-- 4ª demostración (automática)
example : ∀ m n : ℕ, even n → even (m * n) :=
  by intros; simp * with parity_simps

-- Comentarios:
-- 1. Al poner el curso en la línea 1 sobre data.nat.parity y pulsar M-.
--    se abre la teoría correspondiente.
-- 2. Se activa la ventana de objetivos (*Lean Goal*) pulsando C-c C-g
-- 3. Al mover el cursor sobre las pruebas se actualiza la ventana de
--    objetivos.
