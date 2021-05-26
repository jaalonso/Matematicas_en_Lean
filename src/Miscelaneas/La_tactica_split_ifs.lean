-- La táctica split_ifs
-- ====================

import tactic

variables {α : Type*} [decidable_eq α]

-- 1ª demostración
example
  (a b : α)
  : ite (a = b) a b = b :=
begin
  split_ifs,
  { exact h, },
  { refl, }
end

-- 2ª demostración
example
  (a b : α)
  : ite (a = b) a b = b :=
begin
  rw ite_eq_right_iff,
  rw imp_self,
  trivial,
end

-- 3ª demostración
example
  (a b : α)
  : ite (a = b) a b = b :=
by simp only [ite_eq_right_iff, imp_self]

-- 4ª demostración
example
  (a b : α)
  : ite (a = b) a b = b :=
-- by library_search
ite_eq_right_iff.mpr id

-- 5ª demostración
example
  (a b : α)
  : ite (a = b) a b = b :=
-- by hint
by simp
