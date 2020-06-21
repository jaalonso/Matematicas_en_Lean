import data.real.basic

section
variables a b c : ℝ

#check a
-- | a : ℝ

#check a + b
-- | a + b : ℝ

#check (a : ℝ)
-- | a : ℝ

#check mul_comm a b
-- | mul_comm a b : a * b = b * a

#check (mul_comm a b : a * b = b * a)
-- | mul_comm a b : a * b = b * a

#check mul_assoc c a b
-- | mul_assoc c a b : c * a * b = c * (a * b)

#check mul_comm a
-- | mul_comm a : ∀ (b : ℝ), a * b = b * a 

#check mul_comm
-- | mul_comm : ∀ (a b : ?M_1), a * b = b * a

#check @mul_comm
-- | mul_comm : ∀ {G : Type u_1} [_inst_1 : comm_semigroup G] (a b : G), 
--              a * b = b * a

end
