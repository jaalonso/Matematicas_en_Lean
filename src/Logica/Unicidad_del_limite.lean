import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

open_locale classical

theorem converges_to_unique 
  {s : ℕ → ℝ} 
  {a b : ℝ}
  (sa : converges_to s a) 
  (sb : converges_to s b) 
  : a = b :=
begin
  by_contradiction abne,
  have : abs (a - b) > 0,
  { apply abs_pos_of_ne_zero,
    exact sub_ne_zero_of_ne abne },
  let ε := abs (a - b) / 2,
  have εpos : ε > 0,
  { change abs (a - b) / 2 > 0, 
    linarith },
  cases sa ε εpos with Na hNa,
  cases sb ε εpos with Nb hNb,
  let N := max Na Nb,
  have absa : abs (s N - a) < ε,
  { specialize hNa N,
    apply hNa,
    exact le_max_left Na Nb },
  have absb : abs (s N - b) < ε,
  { specialize hNb N,
    apply hNb,
    exact le_max_right Na Nb },
  have : abs (a - b) < abs (a - b),
    calc abs (a - b)
         = abs ((a - s N) + (s N - b))      : by {congr, ring}
     ... ≤ abs (a - s N) + abs (s N - b)    : by apply abs_add_le_abs_add_abs
     ... = abs (s N - a) + abs (s N - b)    : by rw abs_sub
     ... < ε + ε                            : by exact add_lt_add absa absb
     ... = abs (a - b)                      : by exact add_halves (abs (a - b)),
  exact lt_irrefl _ this
end
