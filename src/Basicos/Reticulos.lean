import order.lattice

variables {α : Type*} [lattice α]
variables x y z : α

#check x ⊓ y -- | x ⊓ y : α
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)

#check x ⊔ y -- | x ⊔ y : α
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right: y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

-- Nota: Para ver cómo se escribe un símbolo, se coloca el cursor sobre el 
-- símbolo y se presiona C-c C-k
--
-- Nota: El ínfimo ⊓ se escribe con \glb de "greatest lower bound"
--
-- Nota: El supremo ⊔ se escribe con \lub de "least upper bound"
-- 
-- Nota: En mathlib se unsa inf o sup para los nombres sobre ínfimo o supremo. 
