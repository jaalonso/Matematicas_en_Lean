import order.lattice

variables {α : Type*} [lattice α]
variables a b c : α

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)) :
  (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c) :=
calc
  (a ⊔ b) ⊓ c = c ⊓ (a ⊔ b)       : by rw inf_comm
          ... = (c ⊓ a) ⊔ (c ⊓ b) : by rw h
          ... = (a ⊓ c) ⊔ (c ⊓ b) : by rw [@inf_comm _ _ c a]  
          ... = (a ⊓ c) ⊔ (b ⊓ c) : by rw [@inf_comm _ _ c b]  

example (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)) :
  (a ⊓ b) ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) :=
calc
  (a ⊓ b) ⊔ c = c ⊔ (a ⊓ b)       : by rw sup_comm
          ... = (c ⊔ a) ⊓ (c ⊔ b) : by rw h
          ... = (a ⊔ c) ⊓ (c ⊔ b) : by rw [@sup_comm _ _ c a]  
          ... = (a ⊔ c) ⊓ (b ⊔ c) : by rw [@sup_comm _ _ c b]  

