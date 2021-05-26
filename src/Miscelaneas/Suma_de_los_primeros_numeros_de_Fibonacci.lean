-- Suma de los primeros números de Fibonacci
-- =========================================

import data.nat.basic
import tactic

def fibonacci : ℕ → ℕ
| 0       := 0
| 1       := 1
| (n + 2) := fibonacci n + fibonacci (n + 1)

def fibonacci_sum : ℕ → ℕ
| 0       := 0
| (n + 1) := fibonacci_sum n + fibonacci (n + 1)

lemma fibonacci_succ_pos
  (n : ℕ)
  : 0 < fibonacci (n + 1) :=
begin
  induction n with n HI,
  { exact nat.one_pos, },
  { dsimp [fibonacci],
    apply nat.lt_add_left,
    exact HI, },
end

lemma closed_form
  {n : ℕ}
  : fibonacci_sum n = fibonacci (n + 2) - 1 :=
begin
  induction n with n HI,
  { refl, },
  { dsimp [fibonacci_sum],
    rw HI,
    dsimp [fibonacci],
    have h := fibonacci_succ_pos n,
    omega, },
end
