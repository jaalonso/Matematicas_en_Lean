-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    gcd m n = gcd n m
-- ----------------------------------------------------------------------

import data.nat.gcd

open nat

variables k m n : ℕ

-- 1ª demostración
-- ===============

example : gcd m n = gcd n m :=
begin
  have h1 : gcd m n ∣ gcd n m,
    { have h1a : gcd m n ∣ n,
        by exact gcd_dvd_right m n,
      have h1b : gcd m n ∣ m,
        by exact gcd_dvd_left m n,
      show gcd m n ∣ gcd n m,
        by exact dvd_gcd h1a h1b, },
  have h2 : gcd n m ∣ gcd m n,
    { have h2a : gcd n m ∣ m,
        by exact gcd_dvd_right n m,
      have h2b : gcd n m ∣ n,
        by exact gcd_dvd_left n m,
      show gcd n m ∣ gcd m n,
        by exact dvd_gcd h2a h2b, },
  show gcd m n = gcd n m,
    by exact dvd_antisymm h1 h2,
end

-- 2ª demostración
-- ===============

example : gcd m n = gcd n m :=
begin
  apply dvd_antisymm,
  { apply dvd_gcd,
    { exact gcd_dvd_right m n, },
    { exact gcd_dvd_left m n, }},
  { apply dvd_gcd,
    { exact gcd_dvd_right n m, },
    { exact gcd_dvd_left n m, }},
end

-- 3ª demostración
-- ===============

example : gcd m n = gcd n m :=
begin
  apply dvd_antisymm,
  { apply dvd_gcd (gcd_dvd_right m n) (gcd_dvd_left m n)},
  { apply dvd_gcd (gcd_dvd_right n m) (gcd_dvd_left n m)},
end

-- 4ª demostración
-- ===============

example : gcd m n = gcd n m :=
dvd_antisymm
  (dvd_gcd (gcd_dvd_right m n) (gcd_dvd_left m n))
  (dvd_gcd (gcd_dvd_right n m) (gcd_dvd_left n m))

-- 5ª demostración
-- ===============

lemma aux : gcd m n ∣ gcd n m :=
begin
  have h1 : gcd m n ∣ n,
    by exact gcd_dvd_right m n,
  have h2 : gcd m n ∣ m,
    by exact gcd_dvd_left m n,
  show gcd m n ∣ gcd n m,
    by exact dvd_gcd h1 h2,
end

example : gcd m n = gcd n m :=
begin
  apply dvd_antisymm,
  { exact aux m n, },
  { exact aux n m, },
end

-- 6ª demostración
-- ===============

lemma aux2 : gcd m n ∣ gcd n m :=
dvd_gcd (gcd_dvd_right m n) (gcd_dvd_left m n)

example : gcd m n = gcd n m :=
dvd_antisymm (aux2 m n) (aux2 n m)

-- 7ª demostración
-- ===============

example : gcd m n = gcd n m :=
-- by library_search
gcd_comm m n

-- Lemas usados
-- ============

-- #check (dvd_antisymm : m ∣ n → n ∣ m → m = n)
-- #check (dvd_gcd : k ∣ m → k ∣ n → k ∣ gcd m n)
-- #check (gcd_dvd_left : ∀ (m n : ℕ), gcd m n ∣ m)
-- #check (gcd_dvd_right : ∀ (m n : ℕ), gcd m n ∣ n)
