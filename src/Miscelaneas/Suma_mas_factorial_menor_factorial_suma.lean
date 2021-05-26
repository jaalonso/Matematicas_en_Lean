import data.nat.factorial
import tactic
open nat

localized "notation n `!`:10000 := nat.factorial n" in nat

lemma lt_factorial_self
  {n : ℕ}
  (hi : 3 ≤ n)
  : n < n! :=
begin
  rw [← succ_pred_eq_of_pos ((zero_lt_two.trans (lt.base 2)).trans_le hi), factorial_succ],
  exact lt_mul_of_one_lt_right
        (succ_pos (pred n))
        (calc  1
             < 2         : one_lt_two
         ... ≤ pred n    : le_pred_of_lt (succ_le_iff.mp hi)
         ... ≤ (pred n)! : self_le_factorial (pred n))
end

lemma add_factorial_lt_factorial_add
  {i : ℕ}
  (n : ℕ)
  (hi : 2 ≤ i)
  : i + (n + 1)! < (i + n + 1)! :=
begin
  rw [factorial_succ (i + _), succ_eq_add_one, add_mul, one_mul],
  have : i ≤ i + n := le.intro rfl,
  exact add_lt_add_of_lt_of_le (this.trans_lt ((lt_mul_iff_one_lt_right (zero_lt_two.trans_le
    (hi.trans this))).mpr (lt_iff_le_and_ne.mpr ⟨(i + n).factorial_pos, λ g,
    nat.not_succ_le_self 1 ((hi.trans this).trans (factorial_eq_one.mp g.symm))⟩))) (factorial_le
    ((le_of_eq (add_comm n 1)).trans ((add_le_add_iff_right n).mpr (one_le_two.trans hi)))),
end

lemma add_factorial_lt_factorial_add' {i n : ℕ} (hi : 2 ≤ i) (hn : 1 ≤ n) :
  i + n! < (i + n)! :=
begin
  cases hn,
  { rw factorial_one,
    exact lt_factorial_self (succ_le_succ hi) },
  { exact add_factorial_lt_factorial_add _ hi }
end
