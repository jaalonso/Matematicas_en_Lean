import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

variables {s t : ℕ → ℝ} {a b : ℝ}

theorem converges_to_add
  (cs : converges_to s a) 
  (ct : converges_to t b)
  : converges_to (λ n, s n + t n) (a + b) :=
begin
  intros ε εpos, 
  dsimp,
  have ε2pos : 0 < ε / 2,
    { linarith },
  cases cs (ε / 2) ε2pos with Ns hs,
  cases ct (ε / 2) ε2pos with Nt ht,
  clear cs ct ε2pos εpos,
  use max Ns Nt,
  intros n hn,
  have nNs : n ≥ Ns,
    { exact le_of_max_le_left hn },
  specialize hs n nNs,
  have nNt : n ≥ Nt,
    { exact le_of_max_le_right hn },
  specialize ht n nNt,
  clear hn nNs nNt Ns Nt,
  calc abs (s n + t n - (a + b)) 
           = abs ((s n - a) + (t n -  b))   : by { congr, ring }
       ... ≤ abs (s n - a) + abs (t n -  b) : by apply abs_add
       ... < ε / 2 + ε / 2                  : by linarith [hs, ht]
       ... = ε                              : by apply add_halves
end

