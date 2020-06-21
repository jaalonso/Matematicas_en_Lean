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

example (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 :=
calc
  (a + b) * (a - b)
      = a * (a - b) + b * (a - b)     : by rw add_mul
  ... = a * a - a * b + b * (a - b)   : by rw mul_sub
  ... = a ^ 2 - a * b + b * (a - b)   : by rw pow_two
example (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 :=
calc
  (a + b) * (a - b)
      = a * (a - b) + b * (a - b)     : by rw add_mul
  ... = (a * a - a * b) + b * (a - b) : by rw mul_sub
  ... = (a ^ 2 - a * b) + b * (a - b) : by rw ←pow_two
  ... = (a ^ 2 - a * b) + (b * a - b * b) : by rw mul_sub
sorry

-- -- 1ª demostración
-- example (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 :=
-- begin
--   rw add_mul,
--   rw [mul_sub, mul_sub],
--   rw [←pow_two, ←pow_two],
--   rw add_sub,
--   rw mul_comm,
--   sorry
--   -- rw neg_add_self (b * a),
-- end


