-- Cubo de una diferencia
-- ======================

import tactic

lemma expand_mult
  (α : Type*)
  [integral_domain α]
  [linear_order α]
  (a b : α)
  : (b-a)^3 = b^3-3*a*b^2+3*a^2*b-a^3 :=
by ring_exp
