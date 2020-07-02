-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que los números reales tienen la siguente
-- propiedad 
--    (a * b) * c = b * (a * c)
-- ---------------------------------------------------------------------

import data.real.basic

-- 1ª demostración
-- ===============

example (a b c : ℝ) : (a * b) * c = b * (a * c) :=
begin
  rw mul_comm a b,
  rw mul_assoc b a c,
end

-- Comentarios: 
-- 1. Al colocar el cursor sobre el nombre de un lema se ve su enunciado. 
-- 2. Para completar el nombre de un lema basta escribir parte de su
--    nombre y completar con S-SPC (es decir, simultáneamente las teclas
--    de mayúscula y la de espacio.
-- 3. los lemas usados son
--    + mul_com   : (∀ a b : G),   a * b = b * a
--    + mul_assoc : (∀ a b c : G), (a * b) * c = a * (b * c)
-- 4. La táctica (rw e) (ver https://bit.ly/3eUxbjD) reescribe una
--    expresión usando la ecuación e. 

-- El desarrollo de la prueba es:
-- 
--    inicio
--       a b c : ℝ
--       ⊢ (a * b) * c = b * (a * c)
--    rw mul_comm a b,
--       a b c : ℝ
--       ⊢ (a * b) * c = b * (a * c)   
--    rw mul_assoc b a c
--       no goals

-- 2ª demostración
-- ===============

example 
  (a b c : ℝ) 
  : (a * b) * c = b * (a * c) :=
calc
  (a * b) * c = (b * a) * c : by rw mul_comm a b
          ... = b * (a * c) : by rw mul_assoc b a c

-- Comentario: El entorno calc (ver https://bit.ly/2NRxiAU) permite
-- escribir demostraciones ecuacionales.

-- 3ª demostración
-- ===============

example (a b c : ℝ) : (a * b) * c = b * (a * c) :=
by ring

-- Comentario: La táctica ring demuestra ecuaciones aplicando las
-- propiedades de anillos.



