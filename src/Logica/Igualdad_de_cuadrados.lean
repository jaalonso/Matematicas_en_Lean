-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la teoría de números reales.
-- 2. Declarar x e y como variables sobre los reales.
-- ----------------------------------------------------------------------

import data.real.basic   -- 1
variables (x y : ℝ)      -- 2

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    x^2 = 1
-- entonces
--    x = 1 ∨ x = -1
-- ----------------------------------------------------------------------

example
  (h : x^2 = 1)
  : x = 1 ∨ x = -1 :=
begin
  have h1 : (x - 1) * (x + 1) = 0,
    calc (x - 1) * (x + 1) = x^2 - 1 : by ring
                       ... = 1 - 1   : by rw h
                       ... = 0       : by ring,
  have h2 : x - 1 = 0 ∨ x + 1 = 0,
    { apply eq_zero_or_eq_zero_of_mul_eq_zero h1 },
  cases h2,
  { left,
    exact sub_eq_zero.mp h2 },
  { right,
    exact eq_neg_of_add_eq_zero h2 },
end

-- Prueba
-- ======

/-
x : ℝ,
h : x ^ 2 = 1
⊢ x = 1 ∨ x = -1
  >> have h1 : (x - 1) * (x + 1) = 0,
  >>   calc (x - 1) * (x + 1) = x^2 - 1 : by ring
  >>                      ... = 1 - 1   : by rw h
  >>                      ... = 0       : by ring,
h1 : (x - 1) * (x + 1) = 0
⊢ x = 1 ∨ x = -1
  >> have h2 : x - 1 = 0 ∨ x + 1 = 0,
  >>   { apply eq_zero_or_eq_zero_of_mul_eq_zero h1 },
h2 : x - 1 = 0 ∨ x + 1 = 0
⊢ x = 1 ∨ x = -1
  >> cases h2,
| h2 : x - 1 = 0
| ⊢ x = 1 ∨ x = -1
|   >> { left,
| ⊢ x = 1
|   >>   exact sub_eq_zero.mp h2 },
h2 : x + 1 = 0
⊢ x = 1 ∨ x = -1
  >> { right,
⊢ x = -1
  >>   exact eq_neg_of_add_eq_zero h2 },
no goals
-/

-- Comentario: Se han usado los siguientes lemas
-- + eq_zero_or_eq_zero_of_mul_eq_zero : x * y = 0 → x = 0 ∨ y = 0
-- + sub_eq_zero : x - y = 0 ↔ x = y
-- + eq_neg_of_add_eq_zero : x + y = 0 → x = -y

-- Comprobación
-- #check (@eq_zero_or_eq_zero_of_mul_eq_zero ℝ _ _ _ x y)
-- #check (@sub_eq_zero ℝ _ x y)
-- #check (@eq_neg_of_add_eq_zero ℝ _ x y)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar si
--    x^2 = y^2
-- entonces
--    x = y ∨ x = -y
-- ----------------------------------------------------------------------

example
  (h : x^2 = y^2)
  : x = y ∨ x = -y :=
begin
  have h1 : (x - y) * (x + y) = 0,
    calc (x - y) * (x + y) = x^2 - y^2 : by ring
                       ... = y^2 - y^2 : by rw h
                       ... = 0         : by ring,
  have h2 : x - y = 0 ∨ x + y = 0,
    { apply eq_zero_or_eq_zero_of_mul_eq_zero h1 },
  cases h2,
  { left,
    exact sub_eq_zero.mp h2 },
  { right,
    exact eq_neg_of_add_eq_zero h2 },
end

-- Comentario: Se han usado los siguientes lemas
-- + eq_zero_or_eq_zero_of_mul_eq_zero : x * y = 0 → x = 0 ∨ y = 0
-- + sub_eq_zero : x - y = 0 ↔ x = y
-- + eq_neg_of_add_eq_zero : x + y = 0 → x = -y
