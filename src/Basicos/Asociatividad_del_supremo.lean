import order.lattice

variables {α : Type*} [lattice α]
variables x y z : α

-- 2ª demostración
example : (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z) :=
le_antisymm
  (sup_le
    (sup_le le_sup_left (le_sup_right_of_le le_sup_left))
    (le_sup_right_of_le le_sup_right))
  (sup_le
    (le_sup_left_of_le le_sup_left)
    (sup_le (le_sup_left_of_le le_sup_right) le_sup_right))

-- 2ª demostración
example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := 
sup_assoc
