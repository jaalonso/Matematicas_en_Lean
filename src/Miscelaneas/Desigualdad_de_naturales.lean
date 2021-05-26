-- Desigualdad de naturales
-- ========================

import data.pnat.basic
import tactic

-- 1ª demostración
lemma larger_ineq
  (x y z: ℕ+)
  (h: x + z < y)
  : ¬ x + 2 * z + (y - x - z) < z :=
begin
  cases x with x hx,
  cases y with y hy,
  cases z with z hz,
  simp [← pnat.coe_lt_coe] at ⊢ h,
  linarith,
end
