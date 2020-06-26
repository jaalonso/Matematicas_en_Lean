import data.real.basic

variables (u v w : ℕ → ℝ) (l l' : ℝ)

notation `|`x`|` := abs x

-- l es el límite de la sucesión u
def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

-- 1ª demostración
example 
  (hu : seq_limit u l) 
  (hw : seq_limit w l)
  (h : ∀ n, u n ≤ v n)
  (h' : ∀ n, v n ≤ w n) : 
  seq_limit v l :=
begin
  intros ε hε,
  cases hu ε hε with N hN,
  cases hw ε hε with M hM,
  use (max N M),
  intros n hn,
  specialize hN n (le_of_max_le_left hn),
  specialize hM n (le_of_max_le_right hn),
  rw [abs_le] at *,
  specialize h n,
  specialize h' n,
  split; linarith,
end

-- 2ª demostración
example 
  (hu : seq_limit u l) 
  (hw : seq_limit w l)
  (h : ∀ n, u n ≤ v n)
  (h' : ∀ n, v n ≤ w n) : 
  seq_limit v l :=
begin
  intros ε hε,
  cases hu ε hε with N hN,
  cases hw ε hε with M hM,
  use (max N M),
  intros n hn,
  specialize hN n (le_of_max_le_left hn),
  specialize hM n (le_of_max_le_right hn),
  rw abs_le at *,
  split; linarith [h n, h' n],
end
