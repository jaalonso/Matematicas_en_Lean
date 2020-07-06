-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
--    1. Importar la teoría de grupo.
--    2. Crear el espacio de nombres my_group
--    3. Declarar G como una variable sobre anillos.
--    4. Declarar a y b como variable sobre G. 
-- ----------------------------------------------------------------------

import algebra.group            -- 1
variables {G : Type*} [group G] -- 2
namespace my_group              -- 3
variables (a b : G)             -- 4

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    a * a⁻¹ = 1
-- ----------------------------------------------------------------------

theorem mul_right_inv : a * a⁻¹ = 1 :=
calc
  a * a⁻¹ = 1 * (a * a⁻¹)                : by rw one_mul
      ... = (1 * a) * a⁻¹                : by rw mul_assoc
      ... = (((a⁻¹)⁻¹ * a⁻¹)  * a) * a⁻¹ : by rw mul_left_inv
      ... = ((a⁻¹)⁻¹ * (a⁻¹  * a)) * a⁻¹ : by rw ← mul_assoc
      ... = ((a⁻¹)⁻¹ * 1) * a⁻¹          : by rw mul_left_inv
      ... = (a⁻¹)⁻¹ * (1 * a⁻¹)          : by rw mul_assoc
      ... = (a⁻¹)⁻¹ * a⁻¹                : by rw one_mul
      ... = 1                            : by rw mul_left_inv

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--    a * 1 = a
-- ----------------------------------------------------------------------

theorem mul_one : a * 1 = a :=
calc
  a * 1 = a * (a⁻¹ * a) : by rw mul_left_inv
    ... = (a * a⁻¹) * a : by rw mul_assoc
    ... = 1 * a         : by rw mul_right_inv
    ... = a             : by rw one_mul

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que si
--     b * a = 1
-- entonces 
--    a⁻¹ = b 
-- ----------------------------------------------------------------------


lemma inv_eq_of_mul_eq_one
  (h : b * a = 1) 
  : a⁻¹ = b :=
calc
  a⁻¹ =  1 * a⁻¹       : by rw one_mul
  ... =  (b * a) * a⁻¹ : by rw h
  ... =  b * (a * a⁻¹) : by rw mul_assoc
  ... =  b * 1         : by rw mul_right_inv
  ... =  b             : by rw mul_one

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que
--    (a * b)⁻¹ = b⁻¹ * a⁻¹
-- ----------------------------------------------------------------------

-- En la demostración se usará el siguiente lema:
lemma mul_inv_rev_aux : (b⁻¹ * a⁻¹) * (a * b) = 1 :=
calc
  (b⁻¹ * a⁻¹) * (a * b) 
      = b⁻¹ * (a⁻¹ * (a * b)) : by rw mul_assoc
  ... = b⁻¹ * ((a⁻¹ * a) * b) : by rw mul_assoc
  ... = b⁻¹ * (1 * b)         : by rw mul_left_inv
  ... = b⁻¹ * b               : by rw one_mul
  ... = 1                     : by rw mul_left_inv

theorem mul_inv_rev : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply inv_eq_of_mul_eq_one,
  rw mul_inv_rev_aux,
end

-- El desarrollo de la prueba es
-- 
--    G : Type u_1,
--    _inst_1 : group G,
--    a b : G
--    ⊢ (a * b)⁻¹ = b⁻¹ * a⁻¹
-- apply inv_eq_of_mul_eq_one,
--    ⊢ b⁻¹ * a⁻¹ * (a * b) = 1
-- rw mul_inv_rev_aux,
--    no goals

-- ---------------------------------------------------------------------
-- Ejercicio 6.  Cerrar el espacio de nombre my_group.
-- ----------------------------------------------------------------------

end my_group
