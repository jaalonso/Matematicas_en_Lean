-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    x ∣ w
-- entonces
--    x ∣ y * (x * z) + x^2 + w^2
-- ----------------------------------------------------------------------

import data.nat.gcd

variables w x y z : ℕ

-- 1ª demostración
-- ===============

example
  (h : x ∣ w)
  : x ∣ y * (x * z) + x^2 + w^2 :=
begin
  have h1 : x ∣ x * z,
    by exact dvd.intro z rfl,
  have h2 : x ∣ y * (x * z),
    by exact dvd_mul_of_dvd_right h1 y,
  have h3 : x ∣ x^2,
    by apply dvd_mul_right,
  have h4 : x ∣ w * w,
    by exact dvd_mul_of_dvd_left h w,
  have h5 : x ∣ w^2,
    by rwa ← pow_two w at h4,
  have h6 : x ∣ y * (x * z) + x^2,
    by exact dvd_add h2 h3,
  show x ∣ y * (x * z) + x^2 + w^2,
    by exact dvd_add h6 h5,
end

-- 2ª demostración
-- ===============

example
  (h : x ∣ w)
  : x ∣ y * (x * z) + x^2 + w^2 :=
begin
  apply dvd_add,
  { apply dvd_add,
    { apply dvd_mul_of_dvd_right,
      apply dvd_mul_right, },
    { rw pow_two,
      apply dvd_mul_right, }},
  { rw pow_two,
    apply dvd_mul_of_dvd_left h, },
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
