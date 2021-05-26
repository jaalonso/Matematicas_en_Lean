import data.nat.prime
import data.nat.parity
import tactic
open nat

-- 1ª demostración
-- ===============

theorem prime_and_prime_succ
  (p : ℕ)
  (hp : prime p)
  (hp' : prime (p + 1))
  : p = 2 :=
begin
  cases prime.eq_two_or_odd hp with H H,
  { exact H, },
  { exfalso,
    cases prime.eq_two_or_odd hp' with H' H',
    { rw succ_inj' at H',
      exact prime.ne_one hp H', },
    { have : even (p + 1),
        { rw ← odd_iff at H,
          cases H with k hk,
          rw ← succ_inj' at hk,
          use [k + 1, hk], },
      rw ← not_even_iff at H',
      exact H' this, } }
end

-- 2ª demostración
-- ===============

lemma eq_two_of_prime_and_even
  {n : ℕ}
  (hn : even n)
  (hn' : prime n)
  : n = 2 :=
begin
  symmetry,
  rw ← prime_dvd_prime_iff_eq prime_two hn',
  exact even_iff_two_dvd.mp hn
end

theorem prime_and_prime_succ_2
  (p : ℕ)
  (hprime : prime p)
  (hprimesucc : prime (p + 1))
  : p = 2 :=
begin
  cases even_or_odd p with hp hp,
  { exact eq_two_of_prime_and_even hp hprime },
  { exfalso,
    apply not_prime_one,
    convert hprime,
    apply add_right_cancel,
    convert (eq_two_of_prime_and_even _ hprimesucc).symm,
    rw even_succ,
    exact odd_iff_not_even.mp hp }
end
