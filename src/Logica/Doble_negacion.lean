-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la librería de tácticas.
-- 2. Habilitar la lógica clásica.
-- 3. Declarar Q como una variable proposicional. 
-- ----------------------------------------------------------------------

import tactic           -- 1
open_locale classical   -- 2
variable (Q : Prop)     -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--     ¬ ¬ Q
-- entonces 
--    Q
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example 
  (h : ¬ ¬ Q) 
  : Q :=
begin 
  by_contradiction h1,
  exact (h h1),
end

-- Prueba
-- ======

/-
Q : Prop,
h : ¬¬Q
⊢ Q
  >> by_contradiction h1,
h1 : ¬Q
⊢ false
  >> exact (h h1),
no goals
-/

-- 2ª demostración
-- ===============

example 
  (h : ¬ ¬ Q) 
  : Q :=
not_not.mp h

-- 2ª demostración
-- ===============

example 
  (h : ¬ ¬ Q) 
  : Q :=
by tauto

-- Comentario: La táctica tauto demuestra las tautologís
-- proposionales.

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si
--    Q
-- entonces 
--    ¬ ¬ Q
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example 
  (h : Q) 
  : ¬ ¬ Q :=
begin
  intro h1,
  exact (h1 h),
end

-- Prueba
-- ======

/-
Q : Prop,
h : Q
⊢ ¬¬Q
  >> intro h1,
h1 : ¬Q
⊢ false
  >> exact (h1 h)
no goals
-/

-- 2ª demostración
-- ===============

example 
  (h : Q) 
  : ¬ ¬ Q :=
not_not.mpr h

-- 3ª demostración
-- ===============

example 
  (h : Q) 
  : ¬ ¬ Q :=
by tauto
