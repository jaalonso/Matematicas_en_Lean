-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar la siguientes acciones:
--    1. Importar la teoría de mcd sobre los naturales.
--    2. Declarar x, y y z como variables sobre los naturales.
-- ----------------------------------------------------------------------

import data.nat.gcd   -- 1
variables x y z : ℕ   -- 2

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    x ∣ y
--    y ∣ z
-- entonces
--    x ∣ z
-- ----------------------------------------------------------------------

example
  (h₀ : x ∣ y)
  (h₁ : y ∣ z)
  : x ∣ z :=
dvd_trans h₀ h₁

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--    x ∣ y * x * z
-- ----------------------------------------------------------------------

example : x ∣ y * x * z :=
begin
  apply dvd_mul_of_dvd_left,
  apply dvd_mul_left
end

-- Su desarrollo es
--
--    ⊢ x ∣ y * x * z
-- apply dvd_mul_of_dvd_left,
--    ⊢ x ∣ y * x
-- apply dvd_mul_left
--    no goals

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que
--    x ∣ x^2
-- ----------------------------------------------------------------------

example : x ∣ x^2 :=
begin
  rw pow_two,
  apply dvd_mul_left
end

-- Su desarrollo es
--
--    ⊢ x ∣ x ^ 2
-- rw pow_two,
--    ⊢ x ∣ x * x
-- apply dvd_mul_left
--    no goals

-- Lemas usados
-- ============

-- #check (dvd_trans : x ∣ y → y ∣ z → x ∣ z)
-- #check (dvd_mul_of_dvd_left : x ∣ y → ∀ (c : ℕ), x ∣ y * c)
-- #check (dvd_mul_left : ∀ (a b : ℕ), a ∣ b * a)
-- #check (pow_two : ∀ (a : ℕ), a ^ 2 = a * a)
