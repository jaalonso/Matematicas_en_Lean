-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que en los retículos se verifica que
--     (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z)
-- ----------------------------------------------------------------------

import order.lattice

variables {α : Type*} [lattice α]
variables x y z : α

-- 1ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
begin
  have h1 : (x ⊓ y) ⊓ z ≤ x ⊓ (y ⊓ z),
    { have h1a : (x ⊓ y) ⊓ z ≤ x, calc
        (x ⊓ y) ⊓ z ≤ x ⊓ y : by exact inf_le_left
                ... ≤ x     : by exact inf_le_left,
      have h1b : (x ⊓ y) ⊓ z ≤ y ⊓ z,
        { have h1b1 : (x ⊓ y) ⊓ z ≤ y, calc
            (x ⊓ y) ⊓ z ≤ x ⊓ y : by exact inf_le_left
                    ... ≤ y     : by exact inf_le_right,
          have h1b2 : (x ⊓ y) ⊓ z ≤ z,
            by exact inf_le_right,
          show (x ⊓ y) ⊓ z ≤ y ⊓ z,
            by exact le_inf h1b1 h1b2, },
      show (x ⊓ y) ⊓ z ≤ x ⊓ (y ⊓ z),
        by exact le_inf h1a h1b, },
  have h2 : x ⊓ (y ⊓ z) ≤ (x ⊓ y) ⊓ z,
    { have h2a : x ⊓ (y ⊓ z) ≤ x ⊓ y,
        { have h2a1 : x ⊓ (y ⊓ z) ≤ x,
            by exact inf_le_left,
          have h2a2 : x ⊓ (y ⊓ z) ≤ y, calc
            x ⊓ (y ⊓ z) ≤ y ⊓ z : by exact inf_le_right
                    ... ≤ y     : by exact inf_le_left,
          show x ⊓ (y ⊓ z) ≤ x ⊓ y,
            by exact le_inf h2a1 h2a2, },
      have h2b : x ⊓ (y ⊓ z) ≤ z, calc
        x ⊓ (y ⊓ z) ≤ y ⊓ z : by exact inf_le_right
                ... ≤ z     : by exact inf_le_right,
      show x ⊓ (y ⊓ z) ≤ (x ⊓ y) ⊓ z,
        by exact le_inf h2a h2b, },
  show (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z),
    by exact le_antisymm h1 h2,
end

-- 2ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
begin
  apply le_antisymm,
  { apply le_inf,
    { apply inf_le_of_left_le inf_le_left, },
    { apply le_inf (inf_le_of_left_le inf_le_right) inf_le_right}},
  {apply le_inf,
    { apply le_inf inf_le_left (inf_le_of_right_le inf_le_left), },
    { apply inf_le_of_right_le inf_le_right, },},
end

-- Su desarrollo es
--
-- ⊢ x ⊓ y ⊓ z = x ⊓ (y ⊓ z)
--    apply le_antisymm,
-- ⊢ x ⊓ y ⊓ z ≤ x ⊓ (y ⊓ z)
-- |   { apply le_inf,
-- | ⊢ x ⊓ y ⊓ z ≤ x
-- | |     { apply inf_le_left_of_le inf_le_left },
-- | ⊢ x ⊓ y ⊓ z ≤ y ⊓ z
-- | |     { apply le_inf (inf_le_left_of_le inf_le_right) inf_le_right}},
-- ⊢ x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z
-- |   {apply le_inf,
-- | ⊢ x ⊓ (y ⊓ z) ≤ x ⊓ y
-- | |     { apply le_inf inf_le_left (inf_le_right_of_le inf_le_left)},
-- | ⊢ x ⊓ (y ⊓ z) ≤ z
--      { apply inf_le_right_of_le inf_le_right, },},
-- no goals

-- 3ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
le_antisymm
  (le_inf
    (inf_le_of_left_le inf_le_left)
    (le_inf (inf_le_of_left_le inf_le_right) inf_le_right))
  (le_inf
    (le_inf inf_le_left (inf_le_of_right_le inf_le_left))
    (inf_le_of_right_le inf_le_right))

-- 4ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
-- by library_search
inf_assoc

-- 5ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
-- by hint
by finish
