import tactic
import algebra.group_power.basic
import data.int.gcd

-- 1ª demostración
example
  (a b : ℤ)
  : a * a ∣ b * b → a ∣ b :=
begin
  intro h,
  rw ← pow_two at h,
  rw ← pow_two at h,
  rw int.pow_dvd_pow_iff at h,
  { exact h, },
  { norm_num, },
end

-- 2ª demostración
example
  (a b : ℤ)
  : a * a ∣ b * b → a ∣ b :=
begin
  intro h,
  rw [← pow_two, ← pow_two, int.pow_dvd_pow_iff] at h,
  exact h,
  norm_num,
end

-- 3ª demostración
example
  (a b : ℤ)
  : a * a ∣ b * b → a ∣ b :=
by simp [← pow_two, int.pow_dvd_pow_iff]
