import algebra.group

variables {G : Type*} [group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

namespace my_group

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 :=
calc
  a * a⁻¹ = 1 * (a * a⁻¹)                : by rw one_mul
      ... = (1 * a) * a⁻¹                : by rw mul_assoc
      ... = (((a⁻¹)⁻¹ * a⁻¹)  * a) * a⁻¹ : by rw mul_left_inv
      ... = ((a⁻¹)⁻¹ * (a⁻¹  * a)) * a⁻¹ : by rw ← mul_assoc
      ... = ((a⁻¹)⁻¹ * 1) * a⁻¹          : by rw mul_left_inv
      ... = (a⁻¹)⁻¹ * (1 * a⁻¹)          : by rw mul_assoc
      ... = (a⁻¹)⁻¹ * a⁻¹                : by rw one_mul
      ... = 1                            : by rw mul_left_inv

theorem mul_one (a : G) : a * 1 = a :=
calc
  a * 1 = a * (a⁻¹ * a) : by rw mul_left_inv
    ... = (a * a⁻¹) * a : by rw mul_assoc
    ... = 1 * a         : by rw mul_right_inv
    ... = a             : by rw one_mul

lemma inv_eq_of_mul_eq_one (a b : G) (h : b * a = 1) : a⁻¹ = b :=
calc
  a⁻¹ =  1 * a⁻¹       : by rw one_mul
  ... =  (b * a) * a⁻¹ : by rw h
  ... =  b * (a * a⁻¹) : by rw mul_assoc
  ... =  b * 1         : by rw mul_right_inv
  ... =  b             : by rw mul_one

lemma mul_inv_rev_aux (a b : G) : (b⁻¹ * a⁻¹) * (a * b) = 1 :=
calc
  (b⁻¹ * a⁻¹) * (a * b) 
      = b⁻¹ * (a⁻¹ * (a * b)) : by rw mul_assoc
  ... = b⁻¹ * ((a⁻¹ * a) * b) : by rw mul_assoc
  ... = b⁻¹ * (1 * b)         : by rw mul_left_inv
  ... = b⁻¹ * b               : by rw one_mul
  ... = 1                     : by rw mul_left_inv

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply inv_eq_of_mul_eq_one,
  rw mul_inv_rev_aux,
end

end my_group
