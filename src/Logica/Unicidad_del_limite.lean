-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar la unicidad de los límites de las sucesiones
-- convergentes.
-- ----------------------------------------------------------------------

import .Definicion_de_convergencia

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
  { apply abs_pos.mpr,
    exact sub_ne_zero_of_ne abne,
    exact ordered_add_comm_monoid.to_covariant_class_left ℝ, },
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
         = abs ((a - s N) + (s N - b))      : by {congr, ring_nf}
     ... ≤ abs (a - s N) + abs (s N - b)    : abs_add (a - s N) (s N - b)
     ... = abs (s N - a) + abs (s N - b)    : by rw abs_sub_comm
     ... < ε + ε                            : by exact add_lt_add absa absb
     ... = abs (a - b)                      : by exact add_halves (abs (a - b)),
  exact lt_irrefl _ this,
end

-- Prueba
-- ======

/-
s : ℕ → ℝ,
a b : ℝ,
sa : converges_to s a,
sb : converges_to s b
⊢ a = b
  >> by_contradiction abne,
abne : ¬a = b
⊢ false
  >> have : abs (a - b) > 0,
| ⊢ abs (a - b) > 0
|   >> { apply abs_pos_of_ne_zero,
| ⊢ a - b ≠ 0
|   >>   exact sub_ne_zero_of_ne abne },
this : abs (a - b) > 0
⊢ false
  >> let ε := abs (a - b) / 2,
ε : ℝ := abs (a - b) / 2
⊢ false
  >> have εpos : ε > 0,
| ⊢ ε > 0
|   >> { change abs (a - b) / 2 > 0,
| ⊢ abs (a - b) / 2 > 0
|   >>   linarith },
εpos : ε > 0
⊢ false
  >> cases sa ε εpos with Na hNa,
Na : ℕ,
hNa : ∀ (n : ℕ), n ≥ Na → abs (s n - a) < ε
⊢ false
  >> cases sb ε εpos with Nb hNb,
Nb : ℕ,
hNb : ∀ (n : ℕ), n ≥ Nb → abs (s n - b) < ε
⊢ false
  >> let N := max Na Nb,
N : ℕ := max Na Nb
⊢ false
  >> have absa : abs (s N - a) < ε,
| ⊢ abs (s N - a) < ε
|   >> { specialize hNa N,
| hNa : N ≥ Na → abs (s N - a) < ε
| ⊢ abs (s N - a) < ε
|   >>   apply hNa,
| ⊢ N ≥ Na
|   >>   exact le_max_left Na Nb },
absa : abs (s N - a) < ε
⊢ false
  >> have absb : abs (s N - b) < ε,
| ⊢ abs (s N - b) < ε
|   >> { specialize hNb N,
| hNb : N ≥ Nb → abs (s N - b) < ε
| ⊢ abs (s N - b) < ε
|   >>   apply hNb,
| hNb : N ≥ Nb → abs (s N - b) < ε
|   >>   exact le_max_right Na Nb },
absb : abs (s N - b) < ε
⊢ false
  >> have : abs (a - b) < abs (a - b),
  >>   calc abs (a - b)
  >>        = abs ((a - s N) + (s N - b))   : by {congr, ring_nf}
  >>    ... ≤ abs (a - s N) + abs (s N - b) : by apply abs_add_le_abs_add_abs
  >>    ... = abs (s N - a) + abs (s N - b) : by rw abs_sub
  >>    ... < ε + ε                         : by exact add_lt_add absa absb
  >>    ... = abs (a - b)                   : by exact add_halves (abs (a - b)),
this : abs (a - b) < abs (a - b)
⊢ false
  >> exact lt_irrefl _ this,
no goals
-/

-- Comentario: Se han usado los lemas
-- + abs_add_le_abs_add_abs a b : abs (a + b) ≤ abs a + abs b
-- + abs_pos_of_ne_zero : a ≠ 0 → 0 < abs a
-- + abs_sub a b : abs (a - b) = abs (b - a)
-- + add_halves a : a / 2 + a / 2 = a
-- + add_lt_add : a < b → c < d → a + c < b + d
-- + le_max_left a b : a ≤ max a b
-- + le_max_right a b : b ≤ max a b
-- + sub_ne_zero_of_ne : a ≠ b → a - b ≠ 0

-- Comprobación:
-- variables (a b c d : ℝ)
-- #check @abs_pos_of_ne_zero _ _ a
-- #check @sub_ne_zero_of_ne _ _ a b
-- #check @le_max_left _ _ a b
-- #check @le_max_right _ _ a b
-- #check @abs_add_le_abs_add_abs _ _ a b
-- #check @abs_sub _ _ a b
-- #check @add_lt_add _ _ a b c d
-- #check @add_halves _ _ a
