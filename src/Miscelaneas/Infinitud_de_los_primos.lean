import data.nat.prime
import tactic.linarith

open nat

theorem infinitude_of_primes : ∀ N : ℕ, ∃ p ≥ N, prime p :=
begin
  intro N,

  let M := factorial N + 1,
  let p := min_fac M,

  have pp : prime p :=
  begin
    refine min_fac_prime _,
    have : factorial N > 0 := factorial_pos N,
    linarith,
  end,

  use p,
  split,
  { by_contradiction,
    have h₁ : p ∣ factorial N + 1 := min_fac_dvd M,
    have h₂ : p ∣ factorial N := (prime.dvd_factorial pp).mpr (le_of_not_ge h),
    have h : p ∣ 1 := (nat.dvd_add_right h₂).mp h₁,
    exact prime.not_dvd_one pp h, },
  { exact pp, },
end

-- Comentario: Ver su desarrollo en https://youtu.be/b59fpAJ8Mfs
