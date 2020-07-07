-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que en los espacios métricos
--    0 ≤ dist x y 
-- ----------------------------------------------------------------------

import topology.metric_space.basic

variables {X : Type*} [metric_space X]

variables x y : X

-- 1ª demostración
example : 0 ≤ dist x y := 
  have 2 * dist x y ≥ 0,
    from calc 
      2 * dist x y = dist x y + dist x y : by rw two_mul
               ... = dist x y + dist y x : by rw [dist_comm x y]
               ... ≥ dist x x            : by apply dist_triangle
               ... = 0                   : by rw ← dist_self x,
  nonneg_of_mul_nonneg_left this two_pos

-- 2ª demostración
example : 0 ≤ dist x y := 
dist_nonneg



