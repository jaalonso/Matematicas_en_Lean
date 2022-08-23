-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la teoría de anillos.
-- ----------------------------------------------------------------------

import algebra.ring
import tactic

-- ---------------------------------------------------------------------
-- Ejercicio 2. Crear el espacio de nombre my_ring.
-- ----------------------------------------------------------------------

namespace my_ring

-- ---------------------------------------------------------------------
-- Ejercicio 3. Declara R una variable sobre anillos.
-- ----------------------------------------------------------------------

variables {R : Type*} [ring R]

-- ---------------------------------------------------------------------
-- Ejercicio 4. Declarar a, b y c como variables sobre R.
-- ----------------------------------------------------------------------

variables {a b c : R}

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que si
--    a + b = a + c
-- entonces
--    b = c
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

theorem add_left_cancel
  (h : a + b = a + c)
  : b = c :=
calc b
     = 0 + b        : by rw zero_add
 ... = (-a + a) + b : by rw add_left_neg
 ... = -a + (a + b) : by rw add_assoc
 ... = -a + (a + c) : by rw h
 ... = (-a + a) + c : by rw ←add_assoc
 ... = 0 + c        : by rw add_left_neg
 ... = c            : by rw zero_add

-- 2ª demostración
-- ===============

example
  (h : a + b = a + c)
  : b = c :=
begin
  have h1 : -a + (a + b) = -a + (a + c),
    { by exact congr_arg (has_add.add (-a)) h, },
  clear h,
  rw ← add_assoc at h1,
  rw add_left_neg at h1,
  rw zero_add at h1,
  rw ← add_assoc at h1,
  rw add_left_neg at h1,
  rw zero_add at h1,
  exact h1,
end

-- El desarrollo de la prueba es
--
--    R : Type u_1,
--    _inst_1 : ring R,
--    a b c : R,
--    h : a + b = a + c
--    ⊢ b = c
-- have h1 : -a + (a + b) = -a + (a + c),
--    |    ⊢ -a + (a + b) = -a + (a + c)
--    | { by exact congr_arg (has_add.add (-a)) h },
--    h : a + b = a + c,
--    h1 : -a + (a + b) = -a + (a + c)
--    ⊢ b = c
-- clear h,
--    h1 : -a + (a + b) = -a + (a + c)
--    ⊢ b = c
-- rw ← add_assoc at h1,
--    h1 : -a + a + b = -a + (a + c)
--    ⊢ b = c
-- rw add_left_neg at h1,
--    h1 : 0 + b = -a + (a + c)
--    ⊢ b = c
-- rw zero_add at h1,
--    h1 : b = -a + (a + c)
--    ⊢ b = c
-- rw ← add_assoc at h1,
--    h1 : b = -a + a + c
--    ⊢ b = c
-- rw add_left_neg at h1,
--    h1 : b = 0 + c
--    ⊢ b = c
-- rw zero_add at h1,
--    h1 : b = c
--    ⊢ b = c
-- exact h1,
--    no goals

-- 3ª demostración
-- ===============

example
  (h : a + b = a + c)
  : b = c :=
by finish

-- ---------------------------------------------------------------------
-- Ejercicio 6. Demostrar que si
--    a + b = c + b
-- entonces
--    a = c
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

theorem add_right_cancel
  (h : a + b = c + b)
  : a = c :=
calc
  a
      = a + 0        : by rw add_zero
  ... = a + (b + -b) : by rw add_right_neg
  ... = (a + b) + -b : by rw add_assoc
  ... = (c + b) + -b : by rw h
  ... = c + (b + -b) : by rw ← add_assoc
  ... = c + 0        : by rw ← add_right_neg
  ... = c            : by rw add_zero

-- 2ª demostración
-- ===============

example
  (h : a + b = c + b)
  : a = c :=
by finish

-- ---------------------------------------------------------------------
-- Ejercicio 7. Cerrar el espacio de nombre my_ring.
-- ----------------------------------------------------------------------

end my_ring
