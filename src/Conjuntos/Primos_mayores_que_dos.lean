-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que los primos mayores que 2 son impares.
-- ----------------------------------------------------------------------

import data.nat.prime data.nat.parity tactic

open set nat

example : { n | prime n } ∩ { n | n > 2} ⊆ { n | ¬ even n } :=
begin
  intro n,
  simp,
  intro nprime,
  cases prime.eq_two_or_odd nprime with h h,
  { rw h,
    intro,
    linarith },
  { rw even_iff,
    rw h,
    norm_num },
end

-- Prueba
-- ======

/-
⊢ {n : ℕ | n.prime} ∩ {n : ℕ | n > 2} ⊆ {n : ℕ | ¬n.even}
  >> intro n,
n : ℕ
⊢ n ∈ {n : ℕ | n.prime} ∩ {n : ℕ | n > 2} → n ∈ {n : ℕ | ¬n.even}
  >> simp,
⊢ n.prime → 2 < n → ¬n.even
  >> intro nprime,
nprime : n.prime
⊢ 2 < n → ¬n.even
  >> cases prime.eq_two_or_odd nprime with h h,
| h : n = 2
| ⊢ 2 < n → ¬n.even
|   >> { rw h,
| ⊢ 2 < 2 → ¬2.even
|   >>   intro,
| a : 2 < 2
| ⊢ ¬2.even
|   >>   linarith },
h : n % 2 = 1
⊢ 2 < n → ¬n.even
  >> { rw even_iff,
⊢ 2 < n → ¬n % 2 = 0
  >>   rw h,
⊢ 2 < n → ¬1 = 0
  >>   norm_num },
no goals
-/

-- Comentario: Se han usado los lemas
-- + prime.eq_two_or_odd : p.prime → p = 2 ∨ p % 2 = 1
-- + even_iff : even n ↔ n % 2 = 0

variables (n p : ℕ)
-- #check @prime.eq_two_or_odd p
-- #check @even_iff n
