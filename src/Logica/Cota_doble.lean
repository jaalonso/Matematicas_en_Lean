import import data.real.basic                                               -- 1

-- ---------------------------------------------------------------------
-- Ejercicio 1. Deckarar x como variable implícita sobre los reales. 
-- ----------------------------------------------------------------------

variable {x : ℝ} 

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    ∃a, x < a
-- entonces 
--    ∃b, x < b * 2
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example 
  (h : ∃a, x < a) 
  : ∃b, x < b * 2 :=
begin
  cases h with a hxa,
  use a / 2,
  calc x   < a         : hxa
       ... = a / 2 * 2 : (div_mul_cancel a two_ne_zero).symm,
end

-- Prueba
-- ======

/-
x : ℝ,
h : ∃ (a : ℝ), x < a
⊢ ∃ (b : ℝ), x < b * 2
  >> cases h with a hxa,
x a : ℝ,
hxa : x < a
⊢ ∃ (b : ℝ), x < b * 2
  >> use a / 2,
⊢ x < a / 2 * 2
  >> calc x   < a         : hxa
  >>      ... = a / 2 * 2 : (div_mul_cancel a two_ne_zero).symm,
-/

-- Comentario: Se han usado los lemas
-- + div_mul_cancel a : b ≠ 0 → a / b * b = a 
-- + two_ne_zero : 2 ≠ 0 

-- 2ª demostración
-- ===============

example 
  (h : ∃a, x < a) 
  : ∃b, x < b * 2 :=
begin
  cases h with a hxa,
  use a / 2,
  linarith,
end

-- Prueba
-- ======

/-
x : ℝ,
h : ∃ (a : ℝ), x < a
⊢ ∃ (b : ℝ), x < b * 2
  >> cases h with a hxa,
hxa : x < a
⊢ ∃ (b : ℝ), x < b * 2
  >> use a / 2,
⊢ x < a / 2 * 2
  >> linarith,
no goals
-/

-- 3ª demostración
-- ===============

example 
  (h : ∃a, x < a) 
  : ∃b, x < b * 2 :=
let ⟨a, hxa⟩ := h in ⟨a/2, by linarith⟩

