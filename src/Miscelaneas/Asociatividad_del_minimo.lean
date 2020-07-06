-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la operación mínimo en los retículos es
-- asociativa; es decir, 
--    (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z)
-- ----------------------------------------------------------------------


import order.lattice
import tactic

variables {α : Type*} [lattice α]
variables x y z : α

-- 1ª demostración
-- ===============

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
begin
  apply le_antisymm,
  { apply le_inf,
    calc
        (x ⊓ y) ⊓ z  ≤ (x ⊓ y)     : inf_le_left
                    ... ≤  x       : inf_le_left,
    apply le_inf,
    calc
        (x ⊓ y) ⊓ z  ≤ (x ⊓ y)     : inf_le_left
                    ... ≤  y       : inf_le_right,
    calc
        (x ⊓ y) ⊓ z  ≤ z           : inf_le_right },
  { apply le_inf,
    apply le_inf,
    calc
        x ⊓ (y ⊓ z)  ≤ x           : inf_le_left,
    calc
        x ⊓ (y ⊓ z)  ≤ (y ⊓ z)     : inf_le_right
                    ... ≤  y       : inf_le_left,
    calc
        x ⊓ (y ⊓ z)  ≤ (y ⊓ z)     : inf_le_right
                    ... ≤  z       : inf_le_right
  }
end

-- 2ª demostración
-- ===============

private meta def infs :=
`[refl <|> 
  {apply inf_le_left_of_le, infs} <|> 
  {apply inf_le_right_of_le, infs}]

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
by apply le_antisymm; repeat {apply le_inf}; {infs}

-- 3ª demostración
-- ===============

meta def tactic.interactive.lattice :=
`[apply le_antisymm; repeat {apply le_inf}; infs]

example : (x ⊓ y) ⊓ z = x ⊓ (y ⊓ z) :=
by lattice

example : x ⊓ y = y ⊓ x :=
by lattice
