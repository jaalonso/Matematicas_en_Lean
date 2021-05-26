-- Conjunto finito correspondiente a un tipo finito
-- ================================================

import data.fintype.basic
import data.set.finite

-- 1ª demostración
example
  {α : Type*}
  {p : α → Prop}
  (h : fintype {x // p x})
  : ∃ (s : finset α), ↑s = { x | p x } :=
set.finite.exists_finset_coe ⟨h⟩

-- 2ª demostración
example
  {α : Type*}
  {p : α → Prop}
  (h : fintype {x // p x})
  : ∃ (s : finset α), ↑s = { x | p x } :=
⟨@set.to_finset _ _ h, @set.coe_to_finset _ _ h⟩
