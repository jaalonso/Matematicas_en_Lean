-- ---------------------------------------------------------------------
-- Ejercicio 1. Demostrar que hay algún número real entre 2 y 3.
-- ----------------------------------------------------------------------

import data.real.basic

-- 1ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3,
    by norm_num,
  show ∃ x : ℝ, 2 < x ∧ x < 3,
    by exact Exists.intro (5 / 2) h,
end

-- 2ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3,
    by norm_num,
  show ∃ x : ℝ, 2 < x ∧ x < 3,
    by exact ⟨5 / 2, h⟩,
end

-- 3ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  use 5 / 2,
  norm_num
end

-- 4ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
⟨5 / 2, by norm_num⟩
