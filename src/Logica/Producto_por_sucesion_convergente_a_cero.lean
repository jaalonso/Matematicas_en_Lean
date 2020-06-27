import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

variables {s t : ℕ → ℝ} {a : ℝ}

lemma exists_abs_le_of_converges_to 
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

lemma aux_l1
  (B ε : ℝ)
  (εpos : ε > 0)
  (Bpos : 0 < B)
  (pos0 : ε / B > 0)
  (n : ℕ)
  (h0 : abs (s n) < B)
  (h1 : abs (t n - 0) < ε / B)
  : abs (s n) * abs (t n - 0) < ε :=
begin 
  by_cases h3 : s n = 0,
    { calc abs (s n) * abs (t n - 0) 
               = abs 0 * abs (t n - 0) : by rw h3 
           ... = 0 * abs (t n - 0)     : by rw abs_zero 
           ... = 0                     : by exact zero_mul (abs (t n - 0))
           ... < ε                     : by exact εpos },
  have h4 : abs (s n) > 0,
    by exact abs_pos_iff.mpr h3,
  clear h3,
  have h5 : abs (s n) * abs (t n - 0) < abs (s n) * (ε / B),
    by exact mul_lt_mul_of_pos_left h1 h4,
  have h6 : abs (s n) * (ε / B) < B * (ε / B),
    by exact mul_lt_mul_of_pos_right h0 pos0,
  have h7 : B ≠ 0,
    by exact ne_of_gt Bpos,
  have h8 : B * (ε / B) = ε,
    calc B * (ε / B) = (B * B⁻¹) * ε : by ring
                 ... = 1 * ε         : by rw mul_inv_cancel h7
                 ... = ε             : by exact one_mul ε,
  have h9 : abs (s n) * abs (t n - 0) < B * (ε / B),
    by exact gt.trans h6 h5,
  rw h8 at h9,
  assumption,
end

lemma aux 
  (cs : converges_to s a) 
  (ct : converges_to t 0) 
  : converges_to (λ n, s n * t n) 0 :=
begin
  intros ε εpos, dsimp,
  rcases exists_abs_le_of_converges_to cs with ⟨N₀, B, h₀⟩,
  have Bpos : 0 < B,
    from lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _)),
  have pos₀ : ε / B > 0,
    from div_pos εpos Bpos,
  cases ct _ pos₀ with N₁ h₁,
  use [max N₀ N₁],
  intros n hn,
  have hn0 : n ≥ N₀,
    { exact le_of_max_le_left hn },
  specialize h₀ n hn0,
  have hn1 : n ≥ N₁,
    { exact le_of_max_le_right hn },
  specialize h₁ n hn1,
  clear cs ct hn hn0 hn1 a N₀ N₁,
  calc 
    abs (s n * t n - 0) 
        = abs (s n * (t n - 0))     : by { congr, ring }
    ... = abs (s n) * abs (t n - 0) : by exact abs_mul (s n) (t n - 0)
    ... < ε                         : by exact aux_l1 B ε εpos Bpos pos₀ n h₀ h₁
end
