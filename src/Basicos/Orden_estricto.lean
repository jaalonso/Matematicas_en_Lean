import order.basic

variables {α : Type*} [partial_order α]
variables x y z : α


#check x < y -- | x < y : Prop 
#check (lt_irrefl x : ¬ x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)
#check (lt_iff_le_and_ne : x < y ↔ x ≤ y ∧ x ≠ y)
