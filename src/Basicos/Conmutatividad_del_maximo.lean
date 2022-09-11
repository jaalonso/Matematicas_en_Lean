-- ---------------------------------------------------------------------
-- Ejercicio. Sean a y b números reales. Demostrar que
--    max a b = max b a
-- ----------------------------------------------------------------------

import data.real.basic

variables a b : ℝ

-- 1ª demostración
-- ===============

example : max a b = max b a :=
begin
  apply le_antisymm,
  { show max a b ≤ max b a,
    apply max_le,
    { apply le_max_right },
    apply le_max_left },
  { show max b a ≤ max a b,
    apply max_le,
    { apply le_max_right },
    apply le_max_left }
end

-- 2ª demostración
-- ===============

example : max a b = max b a :=
begin
  have h : ∀ x y, max x y ≤ max y x,
  { intros x y,
    apply max_le,
    apply le_max_right,
    apply le_max_left },
  apply le_antisymm, apply h, apply h
end

-- 3ª demostración
-- ===============

example : max a b = max b a :=
begin
  apply le_antisymm,
  repeat {
    apply max_le,
    apply le_max_right,
    apply le_max_left },
end

-- Lemas usados
-- ============

-- #check (le_max_left a b : a ≤ max a b)
-- #check (le_max_right a b : b ≤ max a b)
-- #check (max_le : a ≤ c → b ≤ c → max a b ≤ c)
