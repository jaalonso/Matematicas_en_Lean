import order.lattice

variables {α : Type*} [lattice α]
variables x y z : α

-- 1ª demostración
-- ===============

example : x ⊔ y = y ⊔ x := 
by apply le_antisymm; simp

-- 2ª demostración
-- ===============

lemma aux : x ⊔ y ≤ y ⊔ x :=
begin
  apply sup_le,
  apply le_sup_right,
  apply le_sup_left,
end

example : x ⊔ y = y ⊔ x := 
begin
  apply le_antisymm,
  apply aux,
  apply aux,
end

-- 3ª demostración
-- ===============

example : x ⊔ y = y ⊔ x := 
sup_comm

-- Lemas usados
-- ============

#check (sup_comm : x ⊔ y = y ⊔ x)
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (le_antisymm : x ≤ y → y ≤ x → x = y) 
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
