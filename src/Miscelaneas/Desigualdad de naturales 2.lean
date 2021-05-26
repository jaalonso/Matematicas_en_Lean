-- Desigualdad de naturales (2)
-- ============================

import tactic
import data.pnat.basic

lemma pnat.add_sub_cancel
  (a b : ℕ+)
  : a + b - b = a :=
pnat.eq
begin
  rw [pnat.sub_coe, if_pos],
  { apply nat.add_sub_cancel },
  { exact lt_add_of_pos_left b.1 a.pos },
end

lemma eq_with_2
  (x z: ℕ+)
  (h2: ¬x + 2 * z < 2 * z)
  : x + 2 * z - 2 * z = x :=
pnat.add_sub_cancel _ _
