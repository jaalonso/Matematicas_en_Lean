-- Forma cerrada de una función recursiva
-- ======================================

import data.nat.basic
import data.real.basic
import tactic

def sequence1 : ℕ → ℕ
  | 0       := 6
  | (n + 1) := 5 + sequence1 n

-- 1ª demostración
example
  { n : ℕ }
  : sequence1 n = 5 * (n + 1) + 1 :=
begin
  induction n with d hd,
  { norm_num [sequence1] },
  { rw [sequence1, hd],
    ring }
end

-- 2ª demostración
example
  { n : ℕ }
  : sequence1 n = 5 * (n + 1) + 1 :=
begin
  induction n with d hd,
  { simp [sequence1], },
  { simp [sequence1, hd],
    ring, }
end

def sequence2 : ℕ → ℕ
  | 0 := 0
  | 1 := 6
  | (n + 1) := 5 + sequence2 n

example
  {n : ℕ}
  (hpos : 0 < n)
  : sequence2 n = 5 * n + 1 :=
begin
  cases n,
  { exact absurd hpos (lt_irrefl _) },
  { induction n with n hn,
    { simp [sequence2] },
    { rw [sequence2, hn nat.succ_pos'],
      ring } }
end
