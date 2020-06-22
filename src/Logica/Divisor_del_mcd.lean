import data.real.basic
import data.nat.gcd

open nat

example : 3 ∣ gcd 6 15 :=
begin
  rw dvd_gcd_iff,
  split; norm_num
end

-- Lemas usados
-- ============

#check dvd_gcd_if -- k | gcd m n ↔ k | m ∧ k | b 
