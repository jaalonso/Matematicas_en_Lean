import algebra.ordered_ring

variables {R : Type*} [ordered_ring R]
variables a b c : R

example : a ≤ b → 0 ≤ b - a := 
begin
  intro h,
  calc 
    0   = a - a : by rw sub_self
    ... ≤ b - a : @add_le_add_right R _ a b h (-a)  
end

example : 0 ≤ b - a → a ≤ b := 
begin
  intro h,
  calc 
    a   = 0 + a       : by rw zero_add
    ... ≤ (b - a) + a : @add_le_add_right R _ 0 (b -a) h a  
    ... = b           : by simp
end

-- 1ª demostración
example (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c := 
begin
  cases classical.em (b ≤ a), { simp [le_antisymm h h₁] },
  cases classical.em (c ≤ 0), { simp [le_antisymm h_1 h₂] },
  exact (le_not_le_of_lt (ordered_semiring.mul_lt_mul_of_pos_right a b c (lt_of_le_not_le h₁ h) (lt_of_le_not_le h₂ h_1))).left,
end

-- 2ª demostración
example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := 
mul_le_mul_of_nonneg_right h h'
