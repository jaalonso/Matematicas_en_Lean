import data.nat.parity tactic
open nat

-- 1ª demostración
example : ∀ m n, even n → even (m * n) :=
  assume m n ⟨k, (hk : n = 2 * k)⟩,
  have hmn : m * n = 2 * (m * k),
    by rw [hk, mul_left_comm],
  show ∃ l, m * n = 2 * l,
    from ⟨_, hmn⟩

-- 2ª demostración (mediante término)
example : ∀ m n, even n → even (m * n) :=
  λ m n ⟨k, hk⟩, ⟨m * k, by rw [hk, mul_left_comm]⟩

-- 3ª demostración (mediante tácticas)
example : ∀ m n, even n → even (m * n) :=
  begin
    rintros m n ⟨k, hk⟩,
    use m * k,
    rw [hk, mul_left_comm]
  end

-- 4ª demostración (mediante tácticas en una línea)
example : ∀ m n, even n → even (m * n) :=
  by rintros m n ⟨k, hk⟩; use m * k; rw [hk, mul_left_comm]

-- 4ª demostración (automática)
example : ∀ m n, even n → even (m * n) :=
  by intros; simp * with parity_simps

-- Notas:
-- + Al poner el curso en la línea 1 sobre data.nat.parity y pulsar M-. 
--   se abre la teoría correspondiente.
-- + Se activa el *Lean Goal* pulsando C-c C-g
-- + Al mover el cursor sobre la prueba se actualiza el *Lean Goal*.

