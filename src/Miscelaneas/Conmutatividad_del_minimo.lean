import order.lattice
import tactic

variables {α : Type*} [lattice α]
variables x y z : α

-- 1ª demostración
-- ===============

example : x ⊓ y = y ⊓ x :=
begin
  apply le_antisymm,
  { apply le_inf,
    apply inf_le_right,
    apply inf_le_left },
  { apply le_inf,
    apply inf_le_right,
    apply inf_le_left },
end

-- 1ª demostración
-- ===============

example : x ⊓ y = y ⊓ x :=
begin
  apply le_antisymm;
  { apply le_inf inf_le_right inf_le_left, },
end
