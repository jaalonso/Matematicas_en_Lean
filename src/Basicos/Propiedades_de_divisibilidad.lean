import data.nat.gcd

variables x y z : ℕ

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
dvd_trans h₀ h₁

example : x ∣ y * x * z :=
begin
  apply dvd_mul_of_dvd_left,
  apply dvd_mul_left
end

example : x ∣ x^2 :=
begin
  rw nat.pow_two,
  apply dvd_mul_left
end

-- Lemas usados
-- ============

#check (dvd_trans : x ∣ y → y ∣ z → x ∣ z)
#check (dvd_mul_of_dvd_left : x ∣ y → ∀ (c : ℕ), x ∣ y * c)
#check (dvd_mul_left : ∀ (a b : ℕ), a ∣ b * a)
#check (nat.pow_two : ∀ (a : ℕ), a ^ 2 = a * a)
