import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]

variables a b : R

#check add_assoc

-- 1ª demostración
theorem neg_add_cancel_right : (a + b) + -b = a :=
begin
  rw add_assoc,
  rw add_right_neg,
  rw add_zero,
end

-- 2ª demostración
theorem neg_add_cancel_right_2 : (a + b) + -b = a :=
by rw [add_assoc, add_right_neg, add_zero]

-- 3ª demostración
theorem neg_add_cancel_right_3 : (a + b) + -b = a :=
calc
  (a + b) + -b 
      = a + (b + -b) : by rw add_assoc
  ... = a + 0        : by rw add_right_neg
  ... = a            : by rw add_zero

end my_ring
