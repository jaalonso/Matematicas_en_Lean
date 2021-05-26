-- Caracterización de coprimos
-- ===========================

import data.int.basic
import data.int.parity
import data.nat.gcd
import ring_theory.int.basic

lemma int.gcd_eq_one_iff_coprime'
  {a b : ℤ}
  : gcd a b = 1 ↔ is_coprime a b :=
by rw [←int.coe_gcd, ←int.coe_nat_one, int.coe_nat_inj', int.gcd_eq_one_iff_coprime]

-- Referencias
-- ===========

-- Ruben Van de Velde "Bezout" https://bit.ly/36qAux0
