import data.real.basic

variables a b c d : ℝ

-- 1ª demostración (con rw)
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
begin
   rw add_mul,
   rw mul_add,
   rw mul_add,
end

-- 2ª demostración (con calc)
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
calc 
  (a + b) * (c + d) 
      = a * (c + d) + b * (c + d)     : by rw add_mul
  ... = a * c + a * d + b * (c + d)   : by rw mul_add
  ... = a * c + a * d + b * c + b * d : by rw mul_add

-- 3ª demostración 
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
by rw [add_mul, mul_add, mul_add]
