-- ---------------------------------------------------------------------
-- Ejercicio 1. Demostrar que si a, b, c, d, e y f son números reales
-- tales que 
--    b * c = e * f
-- entonces
--    ((a * b) * c) * d = ((a * e) * f) * d
-- ---------------------------------------------------------------------

import data.real.basic 

-- 1ª demostración
-- ===============

example 
  (a b c d e f : ℝ) 
  (h : b * c = e * f) 
  : ((a * b) * c) * d = ((a * e) * f) * d :=
begin
  rw mul_assoc a,
  rw h,
  rw ←mul_assoc a,
end

-- El desarrollo de la prueba es
--
-- inicio
--    a b c d e f : ℝ,
--    h : b * c = e * f
--    ⊢ (a * (b * c)) * d = ((a * e) * f) * d
-- rw mul_assoc a,
--    S
--    ⊢ a * (b * c) * d = a * e * f * d
-- rw h,
--    S
--    ⊢ a * (e * f) * d = a * e * f * d
-- rw ←mul_assoc a,
--    no goals
--
-- En el desarrollo anterior, S es el conjunto de hipótesis; es decir,
--    S = {a b c d e f : ℝ,
--         h : b * c = e * f}

-- 2ª demostración
-- ===============

example 
  (a b c d e f : ℝ) 
  (h : b * c = e * f) 
  : ((a * b) * c) * d = ((a * e) * f) * d :=
calc
  ((a * b) * c) * d = (a * (b * c)) * d : by rw mul_assoc a
                ... = (a * (e * f)) * d : by rw h
                ... = ((a * e) * f) * d : by rw ←mul_assoc a

-- 3ª demostración
-- ===============

example 
  (a b c d e f : ℝ) 
  (h : b * c = e * f) 
  : ((a * b) * c) * d = ((a * e) * f) * d :=
by finish

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si a, b, c y d son números reales tales
-- que  
--    c = b * a - d 
--    d = a * b
-- entonces
--    c = 0
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example 
  (a b c d : ℝ) 
  (h1 : c = b * a - d) 
  (h2 : d = a * b) 
  : c = 0 :=
begin
  rw h1,
  rw mul_comm,
  rw h2,
  rw sub_self,
end

-- Comentario: El último lema se puede encontrar escribiendo previamente
--    by library_search
-- y afirma que
--    ∀ (a : G), a - a = 0

-- Desarrollo de la prueba:
-- 
-- inicio
--    a b c d : ℝ,
--    h1 : c = b * a - d,
--    h2 : d = a * b
--    ⊢ c = 0
-- rw h1,
--    S
--    ⊢ b * a - d = 0
-- rw mul_comm,
--    S
--    ⊢ a * b - d = 0
-- rw h2,
--    S
--    ⊢ a * b - a * b = 0
-- rw sub_self,
--    no goals
--
-- En el desarrollo anterior, S es el conjunto de hipótesis; es decir,
--    S = {a b c d : ℝ,
--         h1 : c = b * a - d,
--         h2 : d = a * b}

-- 2ª demostración
-- ===============

example 
  (a b c d : ℝ) 
  (h1 : c = b * a - d) 
  (h2 : d = a * b) 
  : c = 0 :=
calc
  c   = b * a - d     : by rw h1
  ... = a * b - d     : by rw mul_comm
  ... = a * b - a * b : by rw h2
  ... = 0             : by rw sub_self

-- 3ª demostración
-- ===============

example 
  (a b c d : ℝ) 
  (h1 : c = b * a - d) 
  (h2 : d = a * b) 
  : c = 0 :=
by finish [mul_comm]
