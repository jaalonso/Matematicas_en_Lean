import data.real.basic

variables a b c d : ℝ

#check pow_two a
-- | pow_two a : a ^ 2 = a * a 

#check mul_sub a b c
-- | mul_sub a b c : a * (b - c) = a * b - a * c 

#check add_mul a b c
-- | add_mul a b c : (a + b) * c = a * c + b * c 

#check add_sub a b c
-- | add_sub a b c : a + (b - c) = a + b - c

#check sub_sub a b c
-- | sub_sub a b c : a - b - c = a - (b + c)

#check add_zero a
-- | add_zero a : a + 0 = a

-- 1ª demostración
example (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 :=
by ring

-- 2ª demostración
example (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 :=
calc
  (a + b) * (a - b)
      = a * (a - b) + b * (a - b)         : by rw add_mul
  ... = (a * a - a * b) + b * (a - b)     : by rw mul_sub
  ... = (a^2 - a * b) + b * (a - b)       : by rw ← pow_two
  ... = (a^2 - a * b) + (b * a - b * b)   : by rw mul_sub
  ... = (a^2 - a * b) + (b * a - b^2)     : by rw ← pow_two
  ... = (a^2 + -(a * b)) + (b * a - b^2)  : by exact rfl
  ... = a^2 + (-(a * b) + (b * a - b^2))  : by rw add_assoc
  ... = a^2 + (-(a * b) + (b * a + -b^2)) : by exact rfl
  ... = a^2 + ((-(a * b) + b * a) + -b^2) : by rw ← add_assoc 
                                               (-(a * b)) (b * a) (-b^2) 
  ... = a^2 + ((-(a * b) + a * b) + -b^2) : by rw mul_comm
  ... = a^2 + (0 + -b^2)                  : by rw neg_add_self (a * b)
  ... = (a^2 + 0) + -b^2                  : by rw ← add_assoc 
  ... = a^2 + -b^2                        : by rw add_zero
  ... = a^2 - b^2                         : by exact rfl


