import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

theorem converges_to_const (a : ℝ) : converges_to (λ x : ℕ, a) a :=
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

example 
  (c ε : ℝ)
  (acpos : 0 < abs c)
  (εpos : ε > 0)
  : 0 < ε / abs c :=
by exact div_pos εpos acpos


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
       ... = ε                     : by apply mul_div_self
end

example 
  (c ε : ℝ)
  (h : abs c > 0)
  : abs c * (ε / abs c) = ε :=
sorry

example 
  (a b : ℝ)
  (h : b > 0)
  : b * (a / b) = a :=
calc
  b * (a / b)
      = b * (a * b⁻¹) : by exact rfl
  ... = b * (b⁻¹ * a) : by rw mul_comm a b⁻¹
  ... = (b * b⁻¹) * a : by rw ← mul_assoc
  ... = 1 * a         : by rw mul_inv_self 
  ... = a             : by rw one_mul
end
