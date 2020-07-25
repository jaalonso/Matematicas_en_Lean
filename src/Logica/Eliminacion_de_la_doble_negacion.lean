-- ---------------------------------------------------------------------
-- Ejercicio. Importar la librería de tácticas 
-- ----------------------------------------------------------------------

import tactic

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    ¬ ¬ P → P
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  cases classical.em P,
  { assumption },
  { contradiction },
end

-- Prueba
-- ======

/-
P : Prop
⊢ ¬¬P → P
  >> intro h,
h : ¬¬P
⊢ P
  >> cases classical.em P,
| h : ¬¬P
| ⊢ P
|   >> { assumption },
h_1 : ¬P
⊢ P
  >> { contradiction },
no goals
-/

-- 2ª demostración
-- ===============

open classical

example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  cases em P,
  { assumption },
  { contradiction },
end

-- 3ª demostración
-- ===============

open_locale classical

example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  by_cases h' : P,
  { assumption },
  { contradiction },
end

-- Prueba
-- ======

/-
P : Prop
⊢ ¬¬P → P
  >> intro h,
h : ¬¬P
⊢ P
  >> by_cases h' : P,
| 2 goals
| P : Prop,
| h : ¬¬P,
| h' : P
| ⊢ P
|   >> { assumption },
h' : ¬P
⊢ P
  >> { contradiction },
no goals
-/

