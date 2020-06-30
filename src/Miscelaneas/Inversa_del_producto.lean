import algebra.group
import tactic

variables {G : Type*} [group G]

namespace my_group

set_option trace.simplify.rewrite true

-- 1ª demostración
-- ===============

lemma mul_inv_rev 
  (a b : G) 
  : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
inv_eq_of_mul_eq_one $ by simp [mul_assoc]

-- Situando el cursor sobre simp se obtiene
--    [mul_assoc]: a * b * (b⁻¹ * a⁻¹) ==> a * (b * (b⁻¹ * a⁻¹))
--    [mul_inv_cancel_left]: b * (b⁻¹ * a⁻¹) ==> a⁻¹
--    [mul_right_inv]: a * a⁻¹ ==> 1
--    [eq_self_iff_true]: 1 = 1 ==> true
--    [mul_assoc]: a * b * (b⁻¹ * a⁻¹) ==> a * (b * (b⁻¹ * a⁻¹))
--    [mul_inv_cancel_left]: b * (b⁻¹ * a⁻¹) ==> a⁻¹
--    [mul_right_inv]: a * a⁻¹ ==> 1
--    [eq_self_iff_true]: 1 = 1 ==> true

-- 2ª demostración
-- ===============

theorem mul_inv_rev2 
  (a b : G) 
  : (a * b)⁻¹ = b⁻¹ * a ⁻¹ :=
begin
  apply inv_eq_of_mul_eq_one,
  simp only [mul_assoc, mul_inv_cancel_left, mul_right_inv],
end

-- Situando el cursor sobre simp se obtiene
--    [mul_assoc]: a * b * (b⁻¹ * a⁻¹) ==> a * (b * (b⁻¹ * a⁻¹))
--    [mul_inv_cancel_left]: b * (b⁻¹ * a⁻¹) ==> a⁻¹
--    [mul_right_inv]: a * a⁻¹ ==> 1
--    [mul_assoc]: a * b * (b⁻¹ * a⁻¹) ==> a * (b * (b⁻¹ * a⁻¹))
--    [mul_inv_cancel_left]: b * (b⁻¹ * a⁻¹) ==> a⁻¹
--    [mul_right_inv]: a * a⁻¹ ==> 1

-- 3ª demostración
-- ===============

theorem mul_inv_rev3 (a b : G) : (a * b)⁻¹ = b⁻¹ * a ⁻¹ :=
begin
  apply inv_eq_of_mul_eq_one,
  rw [mul_assoc, mul_inv_cancel_left, mul_right_inv],
end

-- 4ª demostración
-- ===============

theorem mul_inv_rev4 (a b : G) : (a * b)⁻¹ = b⁻¹ * a ⁻¹ :=
begin
  apply inv_eq_of_mul_eq_one,
  show (a * b) * (b⁻¹ * a⁻¹) = 1,
  calc (a * b) * (b⁻¹ * a⁻¹) 
           = a * (b * (b⁻¹ * a⁻¹)) : by rw mul_assoc
       ... = a * a⁻¹               : by {congr, rw mul_inv_cancel_left}
       ... = 1                     : by rw mul_right_inv
end

end my_group
