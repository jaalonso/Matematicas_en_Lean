-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
--    1. Importar la teoría de anillos.
--    2. Crear el espacio de nombres my_ring
--    3. Declarar R como una variable sobre anillos.
--    4. Declarar a y b como variables sobre R. 
-- ----------------------------------------------------------------------

import algebra.ring            -- 1
namespace my_ring              -- 2
variables {R : Type*} [ring R] -- 3
variables {a b : R}            -- 4

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    a + b = 0
-- entonces
--    -a = b 
-- ----------------------------------------------------------------------

theorem neg_eq_of_add_eq_zero  
  (h : a + b = 0) 
  : -a = b :=
calc
  -a  = -a + 0       : by rw add_zero
  ... = -a + (a + b) : by rw h
  ... = b            : by rw neg_add_cancel_left

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--     (a + b) + -b = a
-- ----------------------------------------------------------------------

-- 1ª demostración
example : (a + b) + -b = a :=
calc (a + b) + -b = a + (b + -b) : by rw add_assoc
              ... = a + 0        : by rw add_right_neg
              ... = a            : by rw add_zero

-- 2ª demostración
lemma neg_add_cancel_right : (a + b) + -b = a :=
by rw [add_assoc, add_right_neg, add_zero]

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que si 
--    a + b = 0
-- entonces
--    a = -b 
-- ----------------------------------------------------------------------

theorem eq_neg_of_add_eq_zero 
  (h : a + b = 0) 
  : a = -b :=
calc 
  a   = (a + b) + -b : by rw neg_add_cancel_right
  ... = 0 + -b       : by rw h
  ... = -b           : by rw zero_add

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que
--    - 0 = 0 
-- ----------------------------------------------------------------------

theorem neg_zero : (-0 : R) = 0 :=
begin
  apply neg_eq_of_add_eq_zero,
  rw add_zero,
end

-- El desarrollo de la prueba es
-- 
--    R : Type u_1,
--    _inst_1 : ring R
--    ⊢ -0 = 0
-- apply neg_eq_of_add_eq_zero,
--    ⊢ 0 + 0 = 0
-- rw add_zero,
--    no goals

-- ---------------------------------------------------------------------
-- Ejercicio 6. Demostrar que
--     -(-a) = a
-- ----------------------------------------------------------------------

theorem neg_neg : -(-a) = a :=
begin
  apply neg_eq_of_add_eq_zero,
  rw add_left_neg,
end

-- El desarrollo de la prueba es
-- 
--    R : Type u_1,
--    _inst_1 : ring R,
--    a : R
--    ⊢ - -a = a
-- apply neg_eq_of_add_eq_zero,
--    ⊢ -a + a = 0
-- rw add_left_neg,
--    no goals

end my_ring
