-- El comando convert
-- ==================

import topology.basic
open set

lemma image_of_fin_set_is_finite
  (A : Type)
  (B : Type)
  (s : set A)
  (hs : finite s)
  (f : s → B)
  : finite (range f) :=
begin
  convert finite_range _,
  exact hs.fintype
end
