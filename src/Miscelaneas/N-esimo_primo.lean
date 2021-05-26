-- Calcular el n-ésimo número primo.

import data.nat.prime
open nat

def ith_prime : ℕ → ℕ
| 0       := 2
| (i + 1) := nat.find (exists_infinite_primes $ ith_prime i + 1)

-- #eval ith_prime 4

-- Ver https://bit.ly/3aV0Vhs

-- ------------------------------------------------------------------------

def find_prime : ℕ → ℕ → ℕ
| 0 n     := 0
| (i+1) n := by haveI := decidable_prime_1 n;
                exact if prime n then n else find_prime i (n+1)

def ith_prime2 : ℕ → ℕ
| 0 := 2
| (i + 1) := let n := ith_prime2 i in find_prime n (n+1)

example : ith_prime2 4 = 11 := dec_trivial
