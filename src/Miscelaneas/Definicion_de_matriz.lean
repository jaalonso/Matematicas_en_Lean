-- Definición de matriz
-- ====================

import data.matrix.basic

universes u v
variables {n : Type u} [fintype n]
variables {R : Type v} [comm_ring R]

def my_matrix (n : ℕ) : matrix (fin n) (fin n) R
| ⟨0, hn⟩ j := 0
| i j       := 1

lemma my_matrix_def_not_the_first_row
  (n : ℕ)
  (i : fin n)
  (hn : 0 < n)
  (h0 : (⟨0, hn⟩ : fin n) ≠ i)
  (j : fin n)
  : (my_matrix n) i j = (1 : R) :=
begin
  cases n,
  { exact fin_zero_elim i },
  { rcases i with _|i,
    { simpa using h0 },
    { rw my_matrix } }
end
