import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

variables {s : ℕ → ℝ} {a : ℝ}

theorem exists_abs_le_of_converges_to 
  (cs : converges_to s a) 
  : ∃ N b, ∀ n, N ≤ n → abs (s n) < b :=
begin
  cases cs 1 zero_lt_one with N h,
  use [N, abs a + 1],
  intros n hn,
  specialize h n hn,
  calc abs (s n) = abs (s n - a + a)     : by ring 
             ... ≤ abs (s n - a) + abs a : by apply abs_add_le_abs_add_abs
             ... < 1 + abs a             : by exact add_lt_add_right h (abs a)
             ... = abs a + 1             : by exact add_comm 1 (abs a)
end
