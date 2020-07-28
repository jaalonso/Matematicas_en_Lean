-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar si a es el límite de s, entonces
--     ∃ N b, ∀ n, N ≤ n → abs (s n) < b :=
-- ----------------------------------------------------------------------

import .Definicion_de_convergencia

variables {s : ℕ → ℝ} {a : ℝ}

theorem exists_abs_le_of_converges_to 
  (cs : converges_to s a) 
  : ∃ N b, ∀ n, N ≤ n → abs (s n) < b :=
begin
  cases cs 1 zero_lt_one with N h,
  use [N, abs a + 1],
  intros n hn,
  specialize h n hn,
  calc abs (s n) 
           = abs (s n - a + a)     : by ring 
       ... ≤ abs (s n - a) + abs a : by apply abs_add_le_abs_add_abs
       ... < 1 + abs a             : by exact add_lt_add_right h (abs a)
       ... = abs a + 1             : by exact add_comm 1 (abs a),
end

-- Prueba
-- ======

/-
s : ℕ → ℝ,
a : ℝ,
cs : converges_to s a
⊢ ∃ (N : ℕ) (b : ℝ), ∀ (n : ℕ), N ≤ n → abs (s n) < b
  >> cases cs 1 zero_lt_one with N h,
N : ℕ,
h : ∀ (n : ℕ), n ≥ N → abs (s n - a) < 1
⊢ ∃ (N : ℕ) (b : ℝ), ∀ (n : ℕ), N ≤ n → abs (s n) < b
  >> use [N, abs a + 1],
⊢ ∀ (n : ℕ), N ≤ n → abs (s n) < abs a + 1
  >> intros n hn,
n : ℕ,
hn : N ≤ n
⊢ abs (s n) < abs a + 1
  >> specialize h n hn,
h : abs (s n - a) < 1
⊢ abs (s n) < abs a + 1
  >> calc abs (s n) 
  >>          = abs (s n - a + a)     : by ring 
  >>      ... ≤ abs (s n - a) + abs a : by apply abs_add_le_abs_add_abs
  >>      ... < 1 + abs a             : by exact add_lt_add_right h (abs a)
  >>      ... = abs a + 1             : by exact add_comm 1 (abs a),
no goals
-/

-- Comentario: Se usan los lemas
-- + zero_lt_one : 0 < 1  
-- + abs_add_le_abs_add_abs a b : abs (a + b) ≤ abs a + abs b 
-- + add_lt_add_right : a < b → ∀ (c : ℝ), a + c < b + c 
-- + add_comm a b : a + b = b + a 

-- Comprobación:
variable (b : ℝ)
#check @zero_lt_one _ _
#check @abs_add_le_abs_add_abs _ _ a b
#check @add_lt_add_right _ _ a b
#check @add_comm _ _ a b
