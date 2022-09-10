-- ---------------------------------------------------------------------
-- Ejercicio. Sean a, b y c números reales. Demostrar que si
--    a ≤ b
-- entonces
--    c - exp b ≤ c - exp a :=
-- ----------------------------------------------------------------------

import analysis.special_functions.log.basic
import tactic

open real

variables a b c : ℝ

-- 1ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - b ≤ c - a :=
-- by library_search
sub_le_sub_left h c

-- 2ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
begin
   apply sub_le_sub_left _ c,
   apply exp_le_exp.mpr h,
end

-- El desarrollo de la prueba es
--
--    a b c : ℝ,
--    h : a ≤ b
--    ⊢ c - b.exp ≤ c - a.exp
-- apply add_le_add,
-- |    ⊢ c ≤ c
-- | apply le_refl,
--    ⊢ -b.exp ≤ -a.exp
-- apply neg_le_neg,
--    ⊢ a.exp ≤ b.exp
-- apply exp_le_exp.mpr h,
--    no goals

-- 3ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
-- by library_search [exp_le_exp.mpr h]
sub_le_sub_left (exp_le_exp.mpr h) c

-- 4ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
by linarith [exp_le_exp.mpr h]

-- 5ª demostración
-- ===============

example
  (h : a ≤ b)
  : c - exp b ≤ c - exp a :=
-- by hint
by finish

-- Los lemas usados son:
-- #check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
-- #check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
-- #check (le_refl : ∀ (a : real), a ≤ a)
-- #check (neg_le_neg : a ≤ b → -b ≤ -a)
