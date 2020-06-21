import data.nat.gcd

open nat

variables k m n : ℕ

example : gcd m n = gcd n m :=
begin
  apply dvd_antisymm,
  { apply dvd_gcd (gcd_dvd_right m n) (gcd_dvd_left m n)},
  { apply dvd_gcd (gcd_dvd_right n m) (gcd_dvd_left n m)},
end

-- Lemas usados
-- ============

#check (dvd_antisymm : m ∣ n → n ∣ m → m = n)
#check (dvd_gcd : k ∣ m → k ∣ n → k ∣ gcd m n)
#check (gcd_dvd_left : ∀ (m n : ℕ), gcd m n ∣ m)
#check (gcd_dvd_right : ∀ (m n : ℕ), gcd m n ∣ n)
