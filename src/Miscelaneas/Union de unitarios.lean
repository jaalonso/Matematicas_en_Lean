-- Unión de unitarios
-- ==================

import tactic
import data.set.basic

-- 1ª demostración
example
  {R : Type*}
  (s : set R)
  : s = ⋃ (i : s), {i} :=
by ext; simp

-- 2ª demostración
lemma setext
  {R : Type*}
  (s : set R)
  : s = ⋃ (i : s), {i} :=
by tidy
