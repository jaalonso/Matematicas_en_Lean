-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar el límite de la suma de dos sucesiones
-- convergentes es la suma de los límites.
-- ----------------------------------------------------------------------

import .Definicion_de_convergencia

variables {s t : ℕ → ℝ} {a b c : ℝ}

lemma converges_to_add
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
       ... = ε                              : by apply add_halves,
end

-- Prueba
-- ======

/-
s t : ℕ → ℝ,
a b : ℝ,
cs : converges_to s a,
ct : converges_to t b
⊢ converges_to (λ (n : ℕ), s n + t n) (a + b)
  >> intros ε εpos,
ε : ℝ,
εpos : ε > 0
⊢ ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs ((λ (n : ℕ), s n + t n) n - (a + b)) < ε
  >> dsimp,
⊢ ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (s n + t n - (a + b)) < ε
  >> have ε2pos : 0 < ε / 2,
| 2 goals
| s t : ℕ → ℝ,
| a b : ℝ,
| cs : converges_to s a,
| ct : converges_to t b,
| ε : ℝ,
| εpos : ε > 0
| ⊢ 0 < ε / 2
|   >>   { linarith },
s t : ℕ → ℝ,
a b : ℝ,
cs : converges_to s a,
ct : converges_to t b,
ε : ℝ,
εpos : ε > 0,
ε2pos : 0 < ε / 2
⊢ ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (s n + t n - (a + b)) < ε
  >> cases cs (ε / 2) ε2pos with Ns hs,
ε2pos : 0 < ε / 2,
Ns : ℕ,
hs : ∀ (n : ℕ), n ≥ Ns → abs (s n - a) < ε / 2
⊢ ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (s n + t n - (a + b)) < ε
  >> cases ct (ε / 2) ε2pos with Nt ht,
Nt : ℕ,
ht : ∀ (n : ℕ), n ≥ Nt → abs (t n - b) < ε / 2
⊢ ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (s n + t n - (a + b)) < ε
  >> clear cs ct ε2pos εpos,
s t : ℕ → ℝ,
a b ε : ℝ,
Ns : ℕ,
hs : ∀ (n : ℕ), n ≥ Ns → abs (s n - a) < ε / 2,
Nt : ℕ,
ht : ∀ (n : ℕ), n ≥ Nt → abs (t n - b) < ε / 2
⊢ ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs (s n + t n - (a + b)) < ε
  >> use max Ns Nt,
⊢ ∀ (n : ℕ), n ≥ max Ns Nt → abs (s n + t n - (a + b)) < ε
  >> intros n hn,
n : ℕ,
hn : n ≥ max Ns Nt
⊢ abs (s n + t n - (a + b)) < ε
  >> have nNs : n ≥ Ns,
| 2 goals
| s t : ℕ → ℝ,
| a b ε : ℝ,
| Ns : ℕ,
| hs : ∀ (n : ℕ), n ≥ Ns → abs (s n - a) < ε / 2,
| Nt : ℕ,
| ht : ∀ (n : ℕ), n ≥ Nt → abs (t n - b) < ε / 2,
| n : ℕ,
| hn : n ≥ max Ns Nt
| ⊢ n ≥ Ns
|   >>   { exact le_of_max_le_left hn },
nNs : n ≥ Ns
⊢ abs (s n + t n - (a + b)) < ε
  >> specialize hs n nNs,
hs : abs (s n - a) < ε / 2
⊢ abs (s n + t n - (a + b)) < ε
  >> have nNt : n ≥ Nt,
| 2 goals
| s t : ℕ → ℝ,
| a b ε : ℝ,
| Ns Nt : ℕ,
| ht : ∀ (n : ℕ), n ≥ Nt → abs (t n - b) < ε / 2,
| n : ℕ,
| hn : n ≥ max Ns Nt,
| nNs : n ≥ Ns,
| hs : abs (s n - a) < ε / 2
| ⊢ n ≥ Nt
|   >>   { exact le_of_max_le_right hn },
s t : ℕ → ℝ,
a b ε : ℝ,
Ns Nt : ℕ,
ht : ∀ (n : ℕ), n ≥ Nt → abs (t n - b) < ε / 2,
n : ℕ,
hn : n ≥ max Ns Nt,
nNs : n ≥ Ns,
hs : abs (s n - a) < ε / 2,
nNt : n ≥ Nt
⊢ abs (s n + t n - (a + b)) < ε
  >> specialize ht n nNt,
ht : abs (t n - b) < ε / 2
⊢ abs (s n + t n - (a + b)) < ε
  >> clear hn nNs nNt Ns Nt,
s t : ℕ → ℝ,
a b ε : ℝ,
n : ℕ,
hs : abs (s n - a) < ε / 2,
ht : abs (t n - b) < ε / 2
⊢ abs (s n + t n - (a + b)) < ε
  >> calc abs (s n + t n - (a + b))
  >>          = abs ((s n - a) + (t n -  b))   : by { congr, ring }
  >>      ... ≤ abs (s n - a) + abs (t n -  b) : by apply abs_add
  >>      ... < ε / 2 + ε / 2                  : by linarith [hs, ht]
  >>      ... = ε                              : by apply add_halves,
no goals
-/

-- Comentario. Se han usado los lemas:
-- + le_of_max_le_left : max a b ≤ c → a ≤ c
-- + le_of_max_le_right : max a b ≤ c → b ≤ c
-- + abs_add a b : abs (a + b) ≤ abs a + abs b
-- + add_halves a : a / 2 + a / 2 = a

-- Comprobación
-- #check @le_of_max_le_left _ _ a b c
-- #check @le_of_max_le_right _ _ a b c
-- #check @abs_add _ _ a b
-- #check @add_halves _ _ a
