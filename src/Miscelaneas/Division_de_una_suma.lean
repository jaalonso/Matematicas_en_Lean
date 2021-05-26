-- División de una suma
-- ====================

import tactic
import data.nat.modeq

-- 1ª demostración
example
  (a b c : ℕ)
  (hca : c ∣ a)
  (hba : c ∣ b)
  : (a+b)/c=a/c+b/c :=
begin
  cases le_or_gt c 0 with hc hc,
  { rw nat.le_zero_iff at hc,
    rw hc,
    simp only [nat.div_zero] },
  { rw [nat.add_div hc, if_neg, add_zero],
    rw [nat.mod_eq_zero_of_dvd hca, nat.mod_eq_zero_of_dvd hba, add_zero],
    exact hc.lt.not_le, },
end

-- 2ª demostración
example
  (a b c : ℕ)
  (hca : c ∣ a)
  (hba : c ∣ b)
  : (a+b)/c=a/c+b/c :=
if h : c = 0
then by simp [h]
else nat.add_div_eq_of_add_mod_lt
begin
  rw [nat.mod_eq_zero_of_dvd hca,
      nat.mod_eq_zero_of_dvd hba,
      zero_add],
  exact nat.pos_of_ne_zero h,
end

-- ---------------------------------------------------------------------

lemma add_div_of_dvd_right
  {a b c : ℤ}
  (H : c ∣ b)
  : (a + b) / c = a / c + b / c :=
begin
  by_cases h1 : c = 0,
  { simp [h1], },
  { cases H with k hk,
    rw hk,
    change c ≠ 0 at h1,
    rw [mul_comm c k,
        int.add_mul_div_right _ _ h1,
        ← zero_add (k * c),
        int.add_mul_div_right _ _ h1,
        int.zero_div,
        zero_add]},
end

-- ------------------------------------------------------------------------

example
  {a b c : ℤ}
  (H : c ∣ a) :
  (a + b) / c = a / c + b / c :=
by rw [add_comm,
       add_div_of_dvd_right H,
       add_comm]

-- ---------------------------------------------------------------------
