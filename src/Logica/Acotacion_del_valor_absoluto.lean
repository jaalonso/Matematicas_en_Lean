-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar eue si
--    |x + 3| < 5
-- entonces
--    -8 < x < 2
-- ----------------------------------------------------------------------

import data.real.basic

-- 1ª demostración
-- ===============

example 
  (x y : ℝ) 
  : abs (x + 3) < 5 → -8 < x ∧ x < 2 :=
begin
  rw abs_lt,
  intro h,
  split, 
   linarith,
  linarith,
end

-- Prueba
-- ======

/-
x y : ℝ
⊢ abs (x + 3) < 5 → -8 < x ∧ x < 2
  >> rw abs_lt,
⊢ -5 < x + 3 ∧ x + 3 < 5 → -8 < x ∧ x < 2
  >> intro h,
h : -5 < x + 3 ∧ x + 3 < 5
⊢ -8 < x ∧ x < 2
  >> split,
| ⊢ -8 < x  
  >>  linarith,
⊢ x < 2
  >> linarith,
no goals
-/

-- Comentario: El lema usado es
-- + abs_lt: abs a < b ↔ -b < a ∧ a < b

-- 2ª demostración
-- ===============

example 
  (x y : ℝ) 
  : abs (x + 3) < 5 → -8 < x ∧ x < 2 :=
begin
  rw abs_lt,
  intro h,
  split; linarith,
end

-- Comentario: La composición (split; linarith) aplica split y a
-- continuación le aplica linarith a cada subojetivo. 
