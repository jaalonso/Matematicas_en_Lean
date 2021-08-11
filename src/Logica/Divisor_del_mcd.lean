-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que 3 divide al máximo xomún divisor de 6 y 15.
-- ----------------------------------------------------------------------

import data.real.basic
import data.nat.gcd

open nat

-- 1ª demostración
-- ===============

example : 3 ∣ gcd 6 15 :=
begin
  rw dvd_gcd_iff,
  split; norm_num,
end

-- Prueba
-- ======

/-
⊢ 3 ∣ 6.gcd 15
  rw dvd_gcd_iff,
⊢ 3 ∣ 6 ∧ 3 ∣ 15
  split; norm_num,
no goals
-/

-- Comentario: Se ha usado el lema
-- + dvd_gcd_iff: k | gcd m n ↔ k | m ∧ k | b

-- 2ª demostración
-- ===============

example : 3 ∣ gcd 6 15 :=
begin
  convert dvd_refl _,
  by norm_num,
end

-- 3ª demostración
-- ===============

example : 3 ∣ gcd 6 15 :=
by norm_num
