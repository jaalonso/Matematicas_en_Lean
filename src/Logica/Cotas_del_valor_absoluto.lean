-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la teoría de los números reales.
-- 2. Declarar x e y como variables sobre los reales.
-- 3. Iniciar el espacio de nombre my_abs.
-- ----------------------------------------------------------------------

import data.real.basic   -- 1
variables {x y z : ℝ}    -- 2
namespace my_abs         -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    x < abs y ↔ x < y ∨ x < -y
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

theorem lt_abs : x < abs y ↔ x < y ∨ x < -y :=
begin
  unfold abs,
  exact lt_max_iff,
end

-- Prueba
-- ======

/-
x y : ℝ
⊢ x < abs y ↔ x < y ∨ x < -y
  >> unfold abs,
⊢ x < max y (-y) ↔ x < y ∨ x < -y
  >> exact lt_max_iff,
no goals
-/

-- Comentarios:
-- 1. La táctica (unfold e) despliega la definición de e.
-- 2. La definición de abs
--    + abs (a : α) : α := max a (-a)
-- 3. Se ha usado el lema
--    + lt_max_iff : x < max y z ↔ x < y ∨ x < z

-- Comprobación
-- #check (@lt_max_iff ℝ _ x y z)

-- 2ª demostración
-- ===============

example : x < abs y ↔ x < y ∨ x < -y :=
lt_max_iff

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    abs x < y ↔ - y < x ∧ x < y
-- ----------------------------------------------------------------------

theorem abs_lt : abs x < y ↔ -y < x ∧ x < y :=
begin
  unfold abs,
  split,
    { intro h1,
      rw max_lt_iff at h1,
      cases h1 with h2 h3,
      split,
        { exact neg_lt.mp h3 },
        { exact h2 }},
    { intro h4,
      apply max_lt_iff.mpr,
      cases h4 with h5 h6,
      split,
       { exact h6 },
       { exact neg_lt.mp h5 }},
end

-- Prueba
-- ======

/-
x y : ℝ
⊢ abs x < y ↔ -y < x ∧ x < y
  unfold abs,
⊢ max x (-x) < y ↔ -y < x ∧ x < y
  >> split,
| ⊢ max x (-x) < y → -y < x ∧ x < y
|   >>   { intro h1,
| h1 : max x (-x) < y
| ⊢ -y < x ∧ x < y
|   >>     rw max_lt_iff at h1,
| h1 : x < y ∧ -x < y
| ⊢ -y < x ∧ x < y
|   >>     cases h1 with h2 h3,
| h2 : x < y,
| h3 : -x < y
| ⊢ -y < x ∧ x < y
|   >>     split,
| | ⊢ -y < x
|   >>       { exact neg_lt.mp h3 },
| ⊢ x < y
|   >>       { exact h2 }},
⊢ -y < x ∧ x < y → max x (-x) < y
  >>   { intro h4,
h4 : -y < x ∧ x < y
⊢ max x (-x) < y
  >>     apply max_lt_iff.mpr,
⊢ x < y ∧ -x < y
  >>     cases h4 with h5 h6,
h5 : -y < x,
h6 : x < y
⊢ x < y ∧ -x < y
  >>     split,
| ⊢ x < y
  >>      { exact h6 },
⊢ -x < y
  >>      { exact neg_lt.mp h5 }},
no goals
-/

-- Comentarios: Se han usado los siguientes lemas:
-- + max_lt_iff : max x y < z ↔ x < z ∧ y < z
-- + neg_lt : -x < y ↔ -y < x

-- Comprobación:
-- #check (@max_lt_iff ℝ _ x y z)
-- #check (@neg_lt ℝ _ x y)

end my_abs
