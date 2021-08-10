-- Traza_de_reescrituras.lean
-- Traza de reescrituras
-- José A. Alonso Jiménez
-- Sevilla, 10 de agosto de 2021
-- ---------------------------------------------------------------------

import tactic

set_option trace.simplify.rewrite true

example (a b n m : ℕ): (a + b) * (n + m) = a * n + a * m  + b * n + b * m :=
begin
  simp [mul_add, add_assoc, add_mul], -- succeeds
end

-- Escribe
--    0. [simplify.rewrite] [add_mul]: (a + b) * (n + m) ==> a * (n + m) + b * (n + m)
--    0. [simplify.rewrite] [mul_add]: a * (n + m) ==> a * n + a * m
--    0. [simplify.rewrite] [mul_add]: b * (n + m) ==> b * n + b * m
--    0. [simplify.rewrite] [add_assoc]: a * n + a * m + (b * n + b * m) ==> a * n + (a * m + (b * n + b * m))
--    0. [simplify.rewrite] [add_assoc]: a * n + a * m + b * n ==> a * n + (a * m + b * n)
--    0. [simplify.rewrite] [add_assoc]: a * n + (a * m + b * n) + b * m ==> a * n + (a * m + b * n + b * m)
--    0. [simplify.rewrite] [add_assoc]: a * m + b * n + b * m ==> a * m + (b * n + b * m)
--    0. [simplify.rewrite] [add_left_inj]: a * n + (a * m + (b * n + b * m))
--                                          = a * n + (a * m + (b * n + b * m)) ==> a * n = a * n
--    0. [simplify.rewrite] [mul_eq_mul_left_iff]: a * n = a * n ==> n = n ∨ a = 0
--    0. [simplify.rewrite] [eq_self_iff_true]: n = n ==> true
--    0. [simplify.rewrite] [true_or]: true ∨ a = 0 ==> true

example (a b n m : ℕ): (a + b) * (n + m) = a * n + a * m  + b * n + b * m :=
begin
  simp [add_mul, mul_add, add_assoc], -- fails
  sorry
end

-- Escribe:
--    0. [simplify.rewrite] [mul_add]: (a + b) * (n + m) ==> (a + b) * n + (a + b) * m
--    0. [simplify.rewrite] [add_mul]: (a + b) * n ==> a * n + b * n
--    0. [simplify.rewrite] [add_mul]: (a + b) * m ==> a * m + b * m
--    0. [simplify.rewrite] [add_assoc]: a * n + b * n + (a * m + b * m) ==> a * n + (b * n + (a * m + b * m))
--    0. [simplify.rewrite] [add_assoc]: a * n + a * m + b * n ==> a * n + (a * m + b * n)
--    0. [simplify.rewrite] [add_assoc]: a * n + (a * m + b * n) + b * m ==> a * n + (a * m + b * n + b * m)
--    0. [simplify.rewrite] [add_assoc]: a * m + b * n + b * m ==> a * m + (b * n + b * m)
--    0. [simplify.rewrite] [add_right_inj]: a * n + (b * n + (a * m + b * m)) =
--                                           a * n + (a * m + (b * n + b * m)) ==>
--                                           b * n + (a * m + b * m) = a * m + (b * n + b * m)
