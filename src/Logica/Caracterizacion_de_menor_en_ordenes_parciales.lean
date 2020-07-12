-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que en un orden parcial
--     a < b ↔ a ≤ b ∧ a ≠ b
-- ----------------------------------------------------------------------

import tactic

variables {α : Type*} [partial_order α]
variables a b : α

example : a < b ↔ a ≤ b ∧ a ≠ b :=
begin
  rw lt_iff_le_not_le,
  split,
    rintros ⟨h1, h2⟩,
      split,
        exact h1,
        contrapose ! h2,
        rw h2,
    rintros ⟨h3, h4⟩,
      split,
        exact h3,
        contrapose ! h4,
        apply le_antisymm h3 h4,
end

-- Prueba
-- ======

/-α : Type u_1,
_inst_1 : partial_order α,
a b : α
⊢ a < b ↔ a ≤ b ∧ a ≠ b
  >> rw lt_iff_le_not_le,
⊢ a ≤ b ∧ ¬b ≤ a ↔ a ≤ b ∧ a ≠ b
  >> split,
| ⊢ a ≤ b ∧ ¬b ≤ a → a ≤ b ∧ a ≠ b
|   >>   rintros ⟨h1, h2⟩,
| h1 : a ≤ b,
| h2 : ¬b ≤ a
|   >>     split,
| ⊢ a ≤ b ∧ a ≠ b
| | ⊢ a ≤ b
|   >>       exact h1,
| ⊢ a ≠ b
|   >>       contrapose ! h2,
| h2 : a = b
| ⊢ b ≤ a
|   >>       rw h2,
α : Type u_1,
_inst_1 : partial_order α,
a b : α
⊢ a ≤ b ∧ a ≠ b → a ≤ b ∧ ¬b ≤ a
  >>   rintros ⟨h3, h4⟩,
h3 : a ≤ b,
h4 : a ≠ b
⊢ a ≤ b ∧ ¬b ≤ a
  >>     split,
| ⊢ a ≤ b
|   >>       exact h3,
⊢ ¬b ≤ a
  >>       contrapose ! h4,
h4 : b ≤ a
⊢ a = b
  >>       apply le_antisymm h3 h4,
no goals
-/

-- Comentario: Los lemas usados son
-- + lt_iff_le_not_le : a < b ↔ a ≤ b ∧ ¬b ≤ a
-- + le_antisymm : a ≤ b → b ≤ a → a = b
