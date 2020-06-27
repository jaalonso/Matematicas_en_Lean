import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

lemma converges_to_const 
  (a : ℝ) 
  : converges_to (λ x : ℕ, a) a :=
begin
  intros ε εpos, 
  dsimp,
  use 0,
  intros n hn,
  calc abs (a - a) = abs 0 : by { congr, ring }
               ... = 0     : by apply abs_zero
               ... < ε     : by apply εpos
end

variables {s : ℕ → ℝ} {a : ℝ}

lemma converges_to_mul_const_l1
  {c ε : ℝ}
  (h : 0 < c)
  : c * (ε / c) = ε :=
begin
  rw mul_comm,
  have h1 : c ≠ 0,
    by exact ne_of_gt h,
  exact div_mul_cancel ε h1,
end

theorem converges_to_mul_const
  {c : ℝ} 
  (cs : converges_to s a) 
  : converges_to (λ n, c * s n) (c * a) :=
begin
  by_cases h : c = 0,
  { convert converges_to_const 0,
    { ext, rw [h, zero_mul] },
    rw [h, zero_mul] },
  have acpos : 0 < abs c,
    from abs_pos_of_ne_zero h,
  intros ε εpos, 
  dsimp,
  have εcpos : 0 < ε / abs c,
    by exact div_pos εpos acpos,
  cases cs (ε / abs c) εcpos with Ns hs,
  use Ns,
  intros n hn,
  specialize hs n hn,
  calc abs (c * s n - c * a) 
           = abs (c * (s n - a))   : by { congr, ring }
       ... = abs c * abs (s n - a) : by apply abs_mul
       ... < abs c * (ε / abs c)   : by exact mul_lt_mul_of_pos_left hs acpos 
       ... = ε                     : by apply converges_to_mul_const_l1 acpos
end
