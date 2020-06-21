variables {α : Type*} [partial_order α]
variables x y z : α

#check x ≤ y -- | x ≤ y : Prop
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)

-- Nota: Las letras griegas se escriben con \a, \b, ...
