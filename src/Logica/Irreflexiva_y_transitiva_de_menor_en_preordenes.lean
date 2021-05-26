-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la librería de tácticas.
-- 2. Declarar α como una variables sobre preórdenes.
-- 3. Declarar a, b y c como variables sobre elementos de α.
-- ----------------------------------------------------------------------

import tactic                       -- 1
variables {α : Type*} [preorder α]  -- 2
variables a b c : α                 -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 1. Demostrar que que la relación menor es irreflexiva.
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : ¬ a < a :=
begin
  rw lt_iff_le_not_le,
  rintros ⟨h1, h2⟩,
  apply h2 h1,
end

-- Prueba
-- ======

/-
α : Type u_1,
_inst_1 : preorder α,
a : α
⊢ ¬a < a
  >> rw lt_iff_le_not_le,
⊢ ¬(a ≤ a ∧ ¬a ≤ a)
  >> rintros ⟨h1, h2⟩,
h1 : a ≤ a,
h2 : ¬a ≤ a
⊢ false
  >> apply h2 h1,
no goals
-/

-- Comentarios:
-- + La táctica (rintros ⟨h1, h2⟩), si el objetivo es de la forma ¬(P ∧ Q),
--   añade  las hipótesis (h1 : P) y (h2 : Q) y cambia el objetivo a false.
-- + Se ha usado el lema
--      lt_iff_le_not_le : a < b ↔ a ≤ b ∧ ¬b ≤ a

-- 2ª demostración
-- ===============

example : ¬ a < a :=
irrefl a

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que que la relación menor es transitiva.
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : a < b → b < c → a < c :=
begin
  simp only [lt_iff_le_not_le],
  rintros ⟨h1, h2⟩ ⟨h3, h4⟩,
  split,
    apply le_trans h1 h3,
  contrapose ! h4,
  apply le_trans h4 h1,
end

-- Prueba
-- ======

/-
α : Type u_1,
_inst_1 : preorder α,
a b c : α
⊢ a < b → b < c → a < c
  >> simp only [lt_iff_le_not_le],
⊢ a ≤ b ∧ ¬b ≤ a → b ≤ c ∧ ¬c ≤ b → a ≤ c ∧ ¬c ≤ a
  >> rintros ⟨h1, h2⟩ ⟨h3, h4⟩,
h1 : a ≤ b,
h2 : ¬b ≤ a,
h3 : b ≤ c,
h4 : ¬c ≤ b
⊢ a ≤ c ∧ ¬c ≤ a
  >> split,
| ⊢ a ≤ c
  >>   apply le_trans h1 h3,
⊢ ¬c ≤ a
  >> contrapose ! h4,
h4 : c ≤ a
⊢ c ≤ b
  >> apply le_trans h4 h1,
no goals
-/

-- Comentario: Se ha aplicado los lemas
-- + lt_iff_le_not_le : a < b ↔ a ≤ b ∧ ¬b ≤ a
-- + le_trans : a ≤ b → b ≤ c → a ≤ c

-- 2ª demostración
-- ===============

example : a < b → b < c → a < c :=
lt_trans
