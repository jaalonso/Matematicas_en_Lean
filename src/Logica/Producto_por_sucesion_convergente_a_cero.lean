-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar si s es una sucesión convergente y el límite de
-- t es 0, entonces el límite de s * t es 0.
-- ----------------------------------------------------------------------

import .Acotacion_de_convergentes

variables {s t : ℕ → ℝ} {a : ℝ}

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
  { have h4 : abs (s n) > 0,
      by exact abs_pos.mpr h3,
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
      by exact lt_trans h5 h6,
    rw h8 at h9,
    assumption },
end

-- Prueba
-- ======

/-
s t : ℕ → ℝ,
B ε : ℝ,
εpos : ε > 0,
Bpos : 0 < B,
pos0 : ε / B > 0,
n : ℕ,
h0 : abs (s n) < B,
h1 : abs (t n - 0) < ε / B
⊢ abs (s n) * abs (t n - 0) < ε
  >> by_cases h3 : s n = 0,
| h3 : s n = 0
| ⊢ abs (s n) * abs (t n - 0) < ε
|   >> { calc abs (s n) * abs (t n - 0)
|   >>            = abs 0 * abs (t n - 0) : by rw h3
|   >>        ... = 0 * abs (t n - 0)     : by rw abs_zero
|   >>        ... = 0                     : by exact zero_mul (abs (t n - 0))
|   >>        ... < ε                     : by exact εpos },
  >> { have h4 : abs (s n) > 0,
  >>     by exact abs_pos_iff.mpr h3,
h4 : abs (s n) > 0
⊢ abs (s n) * abs (t n - 0) < ε
  >>   clear h3,
  >>   have h5 : abs (s n) * abs (t n - 0) < abs (s n) * (ε / B),
  >>     by exact mul_lt_mul_of_pos_left h1 h4,
h5 : abs (s n) * abs (t n - 0) < abs (s n) * (ε / B)
⊢ abs (s n) * abs (t n - 0) < ε
  >>   have h6 : abs (s n) * (ε / B) < B * (ε / B),
  >>     by exact mul_lt_mul_of_pos_right h0 pos0,
h6 : abs (s n) * (ε / B) < B * (ε / B)
⊢ abs (s n) * abs (t n - 0) < ε
  >>   have h7 : B ≠ 0,
  >>     by exact ne_of_gt Bpos,
h7 : B ≠ 0
⊢ abs (s n) * abs (t n - 0) < ε
  >>   have h8 : B * (ε / B) = ε,
  >>     calc B * (ε / B) = (B * B⁻¹) * ε : by ring
  >>                  ... = 1 * ε         : by rw mul_inv_cancel h7
  >>                  ... = ε             : by exact one_mul ε,
h8 : B * (ε / B) = ε
⊢ abs (s n) * abs (t n - 0) < ε
  >>   have h9 : abs (s n) * abs (t n - 0) < B * (ε / B),
  >>     by exact gt.trans h6 h5,
h9 : abs (s n) * abs (t n - 0) < B * (ε / B)
⊢ abs (s n) * abs (t n - 0) < ε
  >>   rw h8 at h9,
h9 : abs (s n) * abs (t n - 0) < ε
⊢ abs (s n) * abs (t n - 0) < ε
  >>   assumption },
no goals
-/

-- Comentarios: Se han usado los lemas
-- + abs_zero : abs 0 = 0
-- + zero_mul a : 0 * a = 0
-- + abs_pos_iff : 0 < abs a ↔ a ≠ 0
-- + mul_lt_mul_of_pos_left : a < b → 0 < c → c * a < c * b
-- + mul_lt_mul_of_pos_right : a < b → 0 < c → a * c < b * c
-- + ne_of_gt : a > b → a ≠ b
-- + mul_inv_cancel : a ≠ 0 → a * a⁻¹ = 1
-- + one_mul a : 1 * a = a
-- + gt.trans : a > b → b > c → a > c

variables (b c : ℝ)
-- #check @abs_pos_iff _ _ a
-- #check abs_zero
-- #check @gt.trans _ _ a b c
-- #check @mul_inv_cancel _ _ a
-- #check @mul_lt_mul_of_pos_left _ _ a b c
-- #check @mul_lt_mul_of_pos_right _ _ a b c
-- #check @ne_of_gt _ _ a b
-- #check @one_mul _ _ a
-- #check @zero_mul _ _ a

lemma aux
  (cs : converges_to s a)
  (ct : converges_to t 0)
  : converges_to (λ n, s n * t n) 0 :=
begin
  intros ε εpos,
  dsimp,
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
        = abs (s n * (t n - 0))
              : by { congr, ring }
    ... = abs (s n) * abs (t n - 0)
              : by exact abs_mul (s n) (t n - 0)
    ... < ε
              : by exact aux_l1 B ε εpos Bpos pos₀ n h₀ h₁,
end

-- Prueba
-- ======

/-
s t : ℕ → ℝ,
a : ℝ,
cs : converges_to s a,
ct : converges_to t 0
⊢ converges_to (λ (n : ℕ), s n * t n) 0
  >> intros ε εpos,
ε : ℝ,
εpos : ε > 0
⊢ ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs ((λ (n : ℕ), s n * t n) n - 0) < ε
  >> dsimp,
⊢ ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (s n * t n - 0) < ε
  >> rcases exists_abs_le_of_converges_to cs with ⟨N₀, B, h₀⟩,
N₀ : ℕ,
B : ℝ,
h₀ : ∀ (n : ℕ), N₀ ≤ n → abs (s n) < B
⊢ ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (s n * t n - 0) < ε
  >> have Bpos : 0 < B,
  >>   from lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _)),
Bpos : 0 < B
⊢ ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (s n * t n - 0) < ε
  >> have pos₀ : ε / B > 0,
  >>   from div_pos εpos Bpos,
pos₀ : ε / B > 0
⊢ ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (s n * t n - 0) < ε
  >> cases ct _ pos₀ with N₁ h₁,
N₁ : ℕ,
h₁ : ∀ (n : ℕ), n ≥ N₁ → abs (t n - 0) < ε / B
⊢ ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (s n * t n - 0) < ε
  >> use [max N₀ N₁],
⊢ ∀ (n : ℕ), n ≥ max N₀ N₁ → abs (s n * t n - 0) < ε
  >> intros n hn,
n : ℕ,
hn : n ≥ max N₀ N₁
⊢ abs (s n * t n - 0) < ε
  >> have hn0 : n ≥ N₀,
  >>   { exact le_of_max_le_left hn },
hn0 : n ≥ N₀
⊢ abs (s n * t n - 0) < ε
  >> specialize h₀ n hn0,
h₀ : abs (s n) < B
⊢ abs (s n * t n - 0) < ε
  >> have hn1 : n ≥ N₁,
  >>   { exact le_of_max_le_right hn },
hn1 : n ≥ N₁
⊢ abs (s n * t n - 0) < ε
  >> specialize h₁ n hn1,
h₁ : abs (t n - 0) < ε / B
⊢ abs (s n * t n - 0) < ε
  >> clear cs ct hn hn0 hn1 a N₀ N₁,
  >> calc
  >>   abs (s n * t n - 0)
  >>       = abs (s n * (t n - 0))
  >>             : by { congr, ring }
  >>   ... = abs (s n) * abs (t n - 0)
  >>             : by exact abs_mul (s n) (t n - 0)
  >>   ... < ε
  >>             : by exact aux_l1 B ε εpos Bpos pos₀ n h₀ h₁,
no goals
-/

-- Comentarios: Se han usado los lemas
-- + abs_mul : abs (a * b) = abs a * abs b
-- + abs_nonneg a : 0 ≤ abs a
-- + div_pos : 0 < a → 0 < b → 0 < a / b
-- + le_of_max_le_left : max a b ≤ c → a ≤ c
-- + le_of_max_le_right : max a b ≤ c → b ≤ c
-- + lt_of_le_of_lt : a ≤ b → b < c → a < c

-- Comprobación:
-- variables (b c : ℝ)
-- #check @lt_of_le_of_lt _ _ a b c
-- #check @abs_nonneg _ _ a
-- #check @div_pos _ _ a b
-- #check @le_of_max_le_left _ _ a b c
-- #check @le_of_max_le_right _ _ a b c
-- #check abs_mul
