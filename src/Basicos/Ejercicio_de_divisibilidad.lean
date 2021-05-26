-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    x ∣ w
-- entonces
--    x ∣ y * (x * z) + x^2 + w^2
-- ----------------------------------------------------------------------

import data.nat.gcd

variables w x y z : ℕ

example
  (h : x ∣ w)
  : x ∣ y * (x * z) + x^2 + w^2 :=
begin
  apply dvd_add,
    apply dvd_add,
      apply dvd_mul_of_dvd_right,
      apply dvd_mul_right,
    rw pow_two,
    apply dvd_mul_right,
  rw pow_two,
  apply dvd_mul_of_dvd_left h,
end

-- Su desarrollo es
--
-- ⊢ x ∣ y * (x * z) + x ^ 2 + w ^ 2
--    apply dvd_add,
-- ⊢ x ∣ y * (x * z) + x ^ 2
-- |    apply dvd_add,
-- | ⊢ x ∣ y * (x * z)
-- | |    apply dvd_mul_of_dvd_right,
-- | | ⊢ x ∣ x * z
-- | |    apply dvd_mul_right,
-- | ⊢ x ∣ x ^ 2
-- | |    rw pow_two,
-- | | ⊢ x ∣ x * x
-- | |    apply dvd_mul_right,
-- ⊢ x ∣ w ^ 2
-- |    rw pow_two,
-- | ⊢ x ∣ w * w
-- |    apply dvd_mul_of_dvd_left h,
-- no goals

-- Lemas usados
-- ============

-- #check (dvd_add : x ∣ y → x ∣ z → x ∣ y + z)
-- #check (dvd_mul_of_dvd_left : x ∣ y → ∀ (c : ℕ), x ∣ y * c)
-- #check (dvd_mul_of_dvd_right : x ∣ y → ∀ (c : ℕ), x ∣ c * y)
-- #check (dvd_mul_right : ∀ (a b : ℕ), a ∣ a * b)
-- #check (pow_two : ∀ (a : ℕ), a ^ 2 = a * a)
