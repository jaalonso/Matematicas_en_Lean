import data.nat.gcd

variables w x y z : ℕ

example (h : x ∣ w): x ∣ y * (x * z) + x^2 + w^2 :=
begin
  apply dvd_add,
    apply dvd_add,
      apply dvd_mul_of_dvd_right,
      apply dvd_mul_right,
    rw nat.pow_two,
    apply dvd_mul_right,
  rw nat.pow_two,
  apply dvd_mul_of_dvd_left h,  
end

-- Lemas usados
-- ============

#check (dvd_add : x ∣ y → x ∣ z → x ∣ y + z)
#check (dvd_mul_of_dvd_left : x ∣ y → ∀ (c : ℕ), x ∣ y * c)
#check (dvd_mul_of_dvd_right : x ∣ y → ∀ (c : ℕ), x ∣ c * y)
#check (dvd_mul_right : ∀ (a b : ℕ), a ∣ a * b)
#check (nat.pow_two : ∀ (a : ℕ), a ^ 2 = a * a)
