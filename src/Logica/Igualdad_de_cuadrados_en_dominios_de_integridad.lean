-- ---------------------------------------------------------------------
-- Ejercicio. Importar las teorías: 
-- + algebra.group_power de potencias en grupos
-- + tactic de tácticas
-- ----------------------------------------------------------------------

import algebra.group_power 
import tactic

-- ---------------------------------------------------------------------
-- Ejercicio. Declara R como una variable sobre dominios de integridad. 
-- ----------------------------------------------------------------------

variables {R : Type*} [integral_domain R]

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar x e y como variables sobre R. 
-- ----------------------------------------------------------------------

variables (x y : R)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar si
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
