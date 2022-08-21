-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que los productos de los números naturales por
-- números pares son pares.
-- ---------------------------------------------------------------------

import data.nat.parity
import tactic

open nat

-- 1ª demostración
example : ∀ m n : ℕ, even n → even (m * n) :=
begin
  intros m n hn,
  unfold even at *,
  cases hn with k hk,
  use m * k,
  calc m * n
       = m * (k + k)   : congr_arg (has_mul.mul m) hk
   ... = m * k + m * k : mul_add m k k
end

-- 2ª demostración
example : ∀ m n : ℕ, even n → even (m * n) :=
begin
  intros m n hn,
  cases hn with k hk,
  use m * k,
  calc m * n
       = m * (k + k)   : congr_arg (has_mul.mul m) hk
   ... = m * k + m * k : mul_add m k k
end

-- 3ª demostración
example : ∀ m n : ℕ, even n → even (m * n) :=
begin
  rintros m n ⟨k, hk⟩,
  use m * k,
  calc m * n
       = m * (k + k)   : congr_arg (has_mul.mul m) hk
   ... = m * k + m * k : mul_add m k k
end

-- 4ª demostración
example : ∀ m n : ℕ, even n → even (m * n) :=
begin
  rintros m n ⟨k, hk⟩,
  use m * k,
  rw hk,
  exact mul_add m k k,
end

-- 5ª demostración
example : ∀ m n : ℕ, even n → even (m * n) :=
begin
  rintros m n ⟨k, hk⟩,
  use m * k,
  rw [hk, mul_add]
end

-- 6ª demostración
example : ∀ m n : ℕ, even n → even (m * n) :=
begin
  rintros m n ⟨k, hk⟩,
  exact ⟨m * k, by rw [hk, mul_add]⟩
end

-- 7ª demostración
example : ∀ m n : ℕ, even n → even (m * n) :=
λ m n ⟨k, hk⟩, ⟨m * k, by rw [hk, mul_add]⟩

-- 8ª demostración
example : ∀ m n : ℕ, even n → even (m * n) :=
  assume m n ⟨k, (hk : n = k + k)⟩,
  have hmn : m * n = m * k + m * k,
    by rw [hk, mul_add],
  show ∃ l, m * n = l + l,
    from ⟨_, hmn⟩

-- Comentarios:
-- 1. Al poner el curso en la línea 1 sobre data.nat.parity y pulsar M-.
--    se abre la teoría correspondiente.
-- 2. Se activa la ventana de objetivos (*Lean Goal*) pulsando C-c C-g
-- 3. Al mover el cursor sobre las pruebas se actualiza la ventana de
--    objetivos.
