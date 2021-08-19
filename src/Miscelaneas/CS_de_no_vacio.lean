-- CS_de_no_vacio.lean
-- CS de no vacío.
-- José A. Alonso Jiménez
-- Sevilla, 19 de agosto de 2021
-- ---------------------------------------------------------------------

import tactic
open set

variable {C : Type}

-- 1ª demostración
example
  {h: ∃ x : C, x = x}
  : ∃ (X : set C), X ≠ ∅ :=
begin
  apply exists.elim h,
  intros x hx,
  use {x},
  apply nonempty.ne_empty,
  exact singleton_nonempty x,
end

-- 2ª demostración
example
  {h: ∃ x : C, x = x}
  : ∃ (X : set C), X ≠ ∅ :=
begin
  apply exists.elim h,
  intros x hx,
  use {x},
  exact nonempty.ne_empty (singleton_nonempty x),
end

-- 3ª demostración
example
  {h: ∃ x : C, x = x}
  : ∃ (X : set C), X ≠ ∅ :=
begin
  apply exists.elim h,
  intros x hx,
  use [{x}, nonempty.ne_empty (singleton_nonempty x)],
end

-- 4ª demostración
example
  {h: ∃ x : C, x = x}
  : ∃ (X : set C), X ≠ ∅ :=
exists.elim h (λ x hx, by use [{x}, nonempty.ne_empty (singleton_nonempty x)])

-- 5ª demostración
example
  {h: ∃ x : C, x = x}
  : ∃ (X : set C), X ≠ ∅ :=
begin
  obtain ⟨x, hx⟩ := h,
  use [{x}, nonempty.ne_empty (singleton_nonempty x)],
end

-- 6ª demostración
example
  {h: ∃ x : C, x = x}
  : ∃ (X : set C), X ≠ ∅ :=
begin
  cases h with x hx,
  use [{x}, nonempty.ne_empty (singleton_nonempty x)],
end
