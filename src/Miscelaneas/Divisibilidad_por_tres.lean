import data.nat.basic
import tactic.interval_cases

open nat

variable {n : ℕ}

-- 1ª demostración
example :
  (n % 3 = 0) ∨ (n % 3 = 1) ∨ (n % 3 = 2) :=
begin
  induction n with n hn,
  { exact or.inl (zero_mod 3), },
  { rw [succ_eq_add_one, add_mod],
    cases hn with hn hn,
    { rw hn,
      exact or.inr (or.inl rfl) },
    { cases hn with hn hn,
      { rw hn,
        exact or.inr (or.inr rfl) },
      { rw hn,
        exact or.inl rfl }}},
end

-- 1ª demostración
example :
  (n % 3 = 0) ∨ (n % 3 = 1) ∨ (n % 3 = 2) :=
begin
  induction n with n hn,
  { exact or.inl (zero_mod 3), },
  { rw [succ_eq_add_one, add_mod],
    rcases hn with hn | hn | hn;
      { rw hn, tauto }},
end

-- 3ª solución
example :
  (n % 3 = 0) ∨ (n % 3 = 1) ∨ (n % 3 = 2) :=
begin
  have : n % 3 < 3 := mod_lt n zero_lt_three,
  interval_cases n % 3; tauto,
end

-- 4ª demostración
example :
  (n % 3 = 0) ∨ (n % 3 = 1) ∨ (n % 3 = 2) :=
match n % 3, @nat.mod_lt n 3 dec_trivial with
| 0,   _ := or.inl rfl
| 1,   _ := or.inr $ or.inl rfl
| 2,   _ := or.inr $ or.inr rfl
| k+3, h := absurd h dec_trivial
end
