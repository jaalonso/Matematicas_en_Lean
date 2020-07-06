-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si a, b, c, d y e son números reales tales
-- que 
--    a ≤ b
--    b < c
--    c ≤ d
--    d < e
-- entonces
--    a < e 
-- ----------------------------------------------------------------------


import data.real.basic

variables a b c d e : ℝ

-- 1ª demostración
-- ===============

example 
  (h₀ : a ≤ b) 
  (h₁ : b < c) 
  (h₂ : c ≤ d)
  (h₃ : d < e) :
  a < e :=
begin
  apply lt_of_le_of_lt h₀,
  apply lt_trans h₁, 
  apply lt_of_le_of_lt h₂,
  exact h₃,
end

-- El desarrollo de la prueba es
--
--    a b c d e : ℝ,
--    h₀ : a ≤ b,
--    h₁ : b < c,
--    h₂ : c ≤ d,
--    h₃ : d < e
--    ⊢ a < e
-- apply lt_of_le_of_lt h₀,
--    ⊢ b < e
-- apply lt_trans h₁,
--    ⊢ c < e 
-- apply lt_of_le_of_lt h₂,
--    ⊢ d < e
-- exact h₃,
--    no goals

-- 2ª demostración
-- ===============

example 
  (h₀ : a ≤ b) 
  (h₁ : b < c) 
  (h₂ : c ≤ d)
  (h₃ : d < e) :
  a < e :=
calc
  a ≤ b   : h₀
  ... < c : h₁
  ... ≤ d : h₂
  ... < e : h₃

-- 3ª demostración
-- ===============

example 
  (h₀ : a ≤ b) 
  (h₁ : b < c) 
  (h₂ : c ≤ d)
  (h₃ : d < e) :
  a < e :=
by finish
