-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la teoría de anillos.
-- ----------------------------------------------------------------------

import algebra.ring

-- ---------------------------------------------------------------------
-- Ejercicio 2. Crear el espacio de nombres my_ring (para evitar
-- conflictos con los nombres).
-- ----------------------------------------------------------------------

namespace my_ring

-- ---------------------------------------------------------------------
-- Ejercicio 2. Declarar R como una variable implícita sobre los anillos.
-- ----------------------------------------------------------------------

variables {R : Type*} [ring R]

-- ---------------------------------------------------------------------
-- Ejercicio 3. Declarar a como una variable sobre R.
-- ----------------------------------------------------------------------

variable (a : R)

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que
--    a + 0 = a
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : a + 0 = a :=
begin
  rw add_comm,
  rw zero_add,
end

-- El desarrollo de la prueba es
--
--    R : Type u_1,
--    _inst_1 : ring R,
--    a : R
--    ⊢ a + 0 = a
-- rw add_comm,
--    ⊢ 0 + a = a
-- rw zero_add,
--    no goals

-- 2ª demostración
-- ===============

example : a + 0 = a :=
calc
  a + 0 = 0 + a : by rw add_comm
    ... = a     : by rw zero_add


-- 3ª demostración
-- ===============

theorem add_zero : a + 0 = a :=
by rw [add_comm, zero_add]

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que
--    a + -a = 0
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : a + -a = 0 :=
begin
  rw add_comm,
  rw add_left_neg,
end

-- El desarrollo de la prueba es
--
--    R : Type u_1,
--    _inst_1 : ring R,
--    a : R
--    ⊢ a + -a = 0
-- rw add_comm,
--    ⊢ -a + a = 0
-- rw add_left_neg,
--    no goals

-- 2ª demostración
-- ===============

example : a + -a = 0 :=
calc
  a + -a = -a + a : by rw add_comm
     ... = 0 : by rw add_left_neg

-- 3ª demostración
-- ===============

theorem add_right_neg : a + -a = 0 :=
by rw [add_comm, add_left_neg]


-- ---------------------------------------------------------------------
-- Ejercicio 6. Cerrar el espacio de nombre my_ring.
-- ----------------------------------------------------------------------

end my_ring

-- ---------------------------------------------------------------------
-- Ejercicio 7. Calcular el tipo de @my_ring.add_zero.
-- ----------------------------------------------------------------------

-- #check @my_ring.add_zero

-- Comentario: Al colocar el cursor sobre check se obtiene
--    my_ring.add_zero : ∀ {R : Type u_1} [_inst_1 : ring R] (a : R),
--                       a + 0 = a

-- ---------------------------------------------------------------------
-- Ejercicio 8. Calcular el tipo de @add_zero.
-- ----------------------------------------------------------------------

-- #check @add_zero

-- Comentario: Al colocar el cursor sobre check se obtiene
--    add_zero : ∀ {M : Type u_1} [_inst_1 : add_monoid M] (a : M),
--               a + 0 = a
