import data.nat.prime
import data.nat.parity
import tactic
open nat

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

-- 2ª demostración
-- ===============

lemma eq_two_of_prime_and_even2
  (n : ℕ)
  (hn : even n)
  (hn' : prime n)
  : n = 2 :=
begin
  contrapose! hn,
  rw [← odd_iff_not_even, odd_iff],
  exact or.resolve_left (prime.eq_two_or_odd hn') hn,
end
