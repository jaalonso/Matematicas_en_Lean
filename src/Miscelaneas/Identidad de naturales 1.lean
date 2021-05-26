-- Identidad de naturales (1)
-- ==========================

import tactic

example
  (d k : ℕ)
  (h1 : 2 ≠ 0)
  (h2 : 2 * d ^ 2 = 2 * (2 * k * k))
  : d ^ 2 = 2 * k * k :=
-- by library_search
(mul_right_inj' h1).mp h2

example
  (d k : ℕ)
  (h : 2 * d ^ 2 = 2 * (2 * k * k))
  : d ^ 2 = 2 * k * k :=
(mul_right_inj' (by norm_num)).1 h
