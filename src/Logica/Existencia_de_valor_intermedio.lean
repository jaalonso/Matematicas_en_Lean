-- ---------------------------------------------------------------------
-- Ejercicio 1. Demostrar que hay algún número real entre 2 y 3.
-- ----------------------------------------------------------------------

import data.real.basic

-- 1ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  use 5 / 2,
  norm_num
end

-- Su desarrollo es
-- 
-- ⊢ ∃ (x : ℝ), 2 < x ∧ x < 3
--    >> use 5 / 2,
-- ⊢ 2 < 5 / 2 ∧ 5 / 2 < 3
--    >> norm_num
-- no goals

-- Comentarios: 
-- 1. La táctica (use e) (ver https://bit.ly/3iK14Wk) sustituye la
--    variable del objetivo existencial por la expresión e. 
-- 2. La táctica norm_num (ver https://bit.ly/3hoJMgQ) normaliza una
--    expresión numérica. 

-- 2ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3,
    by norm_num,
  exact ⟨5 / 2, h⟩,
end

-- Su desarrollo es
--
-- ⊢ ∃ (x : ℝ), 2 < x ∧ x < 3
--    >> have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3,
--    >>   by norm_num,
-- h : 2 < 5 / 2 ∧ 5 / 2 < 3
-- ⊢ ∃ (x : ℝ), 2 < x ∧ x < 3
--    >> exact ⟨5 / 2, h⟩,
-- no goals

-- Comentario: La táctica (exact ⟨5 / 2, h⟩) sustituye la variable del
-- objetivo por 5/2 y prueba su cuerpo con h.

-- 3ª demostración
-- ===============

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
⟨5 / 2, by norm_num⟩
