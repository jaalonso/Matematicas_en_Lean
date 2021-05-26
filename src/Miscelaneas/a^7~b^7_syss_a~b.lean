-- a^7 = b^7 syss a = b
-- ====================

import tactic
import algebra.ordered_ring

theorem ex_1_3_5
  {α}
  [linear_ordered_ring α]
  (a b : α)
  (h : a^7 = b^7)
  : a = b :=
(@strict_mono_pow_bit1 α _ 3).injective h

-- Referencia
-- ==========

-- Mario Carneiro "if a^7=b^7 then a=b" https://bit.ly/3oyBS6M
