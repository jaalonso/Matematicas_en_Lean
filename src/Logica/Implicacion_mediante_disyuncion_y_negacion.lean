-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (P → Q) ↔ ¬ P ∨ Q 
-- ----------------------------------------------------------------------

import tactic

open_locale classical

-- 1ª demostración
-- ===============

example 
  (P Q : Prop) 
  : (P → Q) ↔ ¬ P ∨ Q :=
begin
  split,
  { intro h1,
    by_cases h2: P,
    { right,
      apply h1,
      exact h2 },
    { left,
      exact h2 }},
  { intros h3 h4,
    cases h3,
    { contradiction },
    { assumption }},
end

-- Prueba
-- ======

/-
P Q : Prop
⊢ P → Q ↔ ¬P ∨ Q
  >> split,
| 2 goals
| P Q : Prop
| ⊢ (P → Q) → ¬P ∨ Q
|   >> { intro h1,
| h1 : P → Q
| ⊢ ¬P ∨ Q
|   >>   by_cases h2: P,
| | 2 goals
| | P Q : Prop,
| | h1 : P → Q,
| | h2 : P
| | ⊢ ¬P ∨ Q
| |   >>   { right,
| | ⊢ Q
| |   >>     apply h1,
| | ⊢ P
| |   >>     exact h2 },
| P Q : Prop,
| h1 : P → Q,
| h2 : ¬P
| ⊢ ¬P ∨ Q
|   >>   { left,
| ⊢ ¬P
|   >>     exact h2 }},
P Q : Prop
⊢ ¬P ∨ Q → P → Q
  >> { intros h3 h4,
h3 : ¬P ∨ Q,
h4 : P
⊢ Q
  >>   cases h3,
| 2 goals
| case or.inl
| P Q : Prop,
| h4 : P,
| h3 : ¬P
| ⊢ Q
|   >>   { contradiction },
case or.inr
P Q : Prop,
h4 : P,
h3 : Q
⊢ Q
  >>   { assumption }},
no goals
-/

-- 2ª demostración
-- ===============

example 
  (P Q : Prop) 
  : (P → Q) ↔ ¬ P ∨ Q :=
imp_iff_not_or

-- 3ª demostración
-- ===============

example 
  (P Q : Prop) 
  : (P → Q) ↔ ¬ P ∨ Q :=
by tauto

