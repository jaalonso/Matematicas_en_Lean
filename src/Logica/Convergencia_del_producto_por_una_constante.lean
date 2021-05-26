-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar si s es una suceción que converge a a y c es un
-- número real, entonces c * s converge a c * a.
-- ----------------------------------------------------------------------

import .Convergencia_de_la_funcion_constante

variables {s : ℕ → ℝ} {a : ℝ}

lemma converges_to_mul_const_l1
  {c ε : ℝ}
  (h : 0 < c)
  : c * (ε / c) = ε :=
begin
  rw mul_comm,
  apply div_mul_cancel ε,
  exact ne_of_gt h,
end

-- Prueba
-- ======

/-
c ε : ℝ,
h : 0 < c
⊢ c * (ε / c) = ε
  >> rw mul_comm,
⊢ ε / c * c = ε
  >> apply div_mul_cancel ε,
⊢ c ≠ 0
  >> exact ne_of_gt h,
no goals
-/

theorem converges_to_mul_const
  {c : ℝ}
  (cs : converges_to s a)
  : converges_to (λ n, c * s n) (c * a) :=
begin
  by_cases h : c = 0,
  { convert converges_to_const 0,
    { ext,
      rw [h, zero_mul] },
    { rw [h, zero_mul] }},
  have acpos : 0 < abs c,
    from abs_pos.mpr h,
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

-- Prueba
-- ======

/-
s : ℕ → ℝ,
a c : ℝ,
cs : converges_to s a
⊢ converges_to (λ (n : ℕ), c * s n) (c * a)
  >> by_cases h : c = 0,
| h : c = 0
| ⊢ converges_to (λ (n : ℕ), c * s n) (c * a)
|   >> { convert converges_to_const 0,
| | ⊢ (λ (n : ℕ), c * s n) = λ (x : ℕ), 0
| |   >>   { ext,
| | x : ℕ
| | ⊢ c * s x = 0
| |   >>     rw [h, zero_mul] },
| s : ℕ → ℝ,
| a c : ℝ,
| cs : converges_to s a,
| h : c = 0
| ⊢ c * a = 0
|   >>   rw [h, zero_mul] },
s : ℕ → ℝ,
a c : ℝ,
cs : converges_to s a,
h : ¬c = 0
⊢ converges_to (λ (n : ℕ), c * s n) (c * a)
  >> have acpos : 0 < abs c,
| ⊢ 0 < abs c
|   >>   from abs_pos_of_ne_zero h,
acpos : 0 < abs c
⊢ converges_to (λ (n : ℕ), c * s n) (c * a)
  >> intros ε εpos,
ε : ℝ,
εpos : ε > 0
⊢ ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs ((λ (n : ℕ), c * s n) n - c * a) < ε
  >> dsimp,
⊢ ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (c * s n - c * a) < ε
  >> have εcpos : 0 < ε / abs c,
  >>   by exact div_pos εpos acpos,
εcpos : 0 < ε / abs c
⊢ ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (c * s n - c * a) < ε
  >> cases cs (ε / abs c) εcpos with Ns hs,
Ns : ℕ,
hs : ∀ (n : ℕ), n ≥ Ns → abs (s n - a) < ε / abs c
⊢ ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (c * s n - c * a) < ε
  >> use Ns,
⊢ ∀ (n : ℕ), n ≥ Ns → abs (c * s n - c * a) < ε
  >> intros n hn,
n : ℕ,
hn : n ≥ Ns
⊢ abs (c * s n - c * a) < ε
  >> specialize hs n hn,
hs : abs (s n - a) < ε / abs c
⊢ abs (c * s n - c * a) < ε
  >> calc abs (c * s n - c * a)
  >>     = abs (c * (s n - a))   : by { congr, ring }
  >> ... = abs c * abs (s n - a) : by apply abs_mul
  >> ... < abs c * (ε / abs c)   : by exact mul_lt_mul_of_pos_left hs acpos
  >> ... = ε                     : by apply converges_to_mul_const_l1-/
/-acpos,
no goals
-/

-- Comentario: Se han usado los lemas
-- + mul_comm a b : a * b = b * a
-- + ne_of_gt : a > b → a ≠ b
-- + converges_to_const a : converges_to (λ (x : ℕ), a) a
-- + zero_mul a : 0 * a = 0
-- + abs_pos_of_ne_zero : a ≠ 0 → 0 < abs a
-- + div_pos : 0 < a → 0 < b → 0 < a / b
-- + abs_mul a b : abs (a * b) = abs a * abs b
-- + mul_lt_mul_of_pos_left : a < b → 0 < d → d * a < d * b

-- Comprobación:
-- variables (b d : ℝ)
-- #check @mul_comm _ _ a b
-- #check @ne_of_gt _ _ a b
-- #check converges_to_const a
-- #check @zero_mul _ _ a
-- #check @abs_pos_of_ne_zero _ _ a
-- #check @div_pos _ _ a b
-- #check @abs_mul _ _ a b
-- #check @mul_lt_mul_of_pos_left _ _ a b d
