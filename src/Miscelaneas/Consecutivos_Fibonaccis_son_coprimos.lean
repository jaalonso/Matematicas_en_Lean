import data.nat.fib
import data.nat.gcd
import tactic

open nat

/-- https://proofwiki.org/wiki/Consecutive_Fibonacci_Numbers_are_Coprime -/
lemma fib_succ_coprime (n : ℕ) : gcd (fib n) (fib $ n + 1) = 1 :=
begin
  induction n with n ih,
  { simp, },
  { convert ih using 1,
    rw [fib_succ_succ, succ_eq_add_one, gcd_rec, add_mod_right, gcd_comm (fib n),
      gcd_rec (fib (n + 1))], },
end

/-- https://proofwiki.org/wiki/Fibonacci_Number_in_terms_of_Smaller_Fibonacci_Numbers -/
lemma fib_add (n m : ℕ) : fib (n + m + 1) = fib (n + 1) * fib (m + 1) + fib n * fib m :=
begin
  induction n with n ih generalizing m ,
  { simp, },
  { rw [(by rw succ_eq_add_one; ac_refl : n.succ + m + 1 = n + (m + 1) + 1), ih,
      fib_succ_succ, fib_succ_succ],
    ring, },
end
