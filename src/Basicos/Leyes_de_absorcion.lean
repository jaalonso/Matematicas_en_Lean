import order.lattice

variables {α : Type*} [lattice α]
variables x y z : α

-- 1ª demostración
example : x ⊓ (x ⊔ y) = x := 
by simp

-- 2ª demostración
example : x ⊓ (x ⊔ y) = x := 
inf_sup_self

-- 1ª demostración
example : x ⊔ (x ⊓ y) = x := 
by simp

-- 2ª demostración
example : x ⊔ (x ⊓ y) = x := 
sup_inf_self
