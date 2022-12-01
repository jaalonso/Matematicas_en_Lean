-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la relación de divisibilidad es transitiva.
-- ----------------------------------------------------------------------

import tactic

variables {a b c : ℕ}

-- 1ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divbc : b ∣ c) :
  a ∣ c :=
begin
  rcases divab with ⟨d, beq : b = a * d⟩,
  rcases divbc with ⟨e, ceq : c = b * e⟩,
  have h1 : c = a * (d * e),
    calc c = b * e       : ceq
       ... = (a * d) * e : congr_arg (* e) beq
       ... = a * (d * e) : mul_assoc a d e,
  show a ∣ c,
    by exact dvd.intro (d * e) (eq.symm h1),
end

-- 2ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divbc : b ∣ c) :
  a ∣ c :=
begin
  cases divab with d beq,
  cases divbc with e ceq,
  rw [ceq, beq],
  use (d * e),
  exact mul_assoc a d e,
end

-- Su desarrollo es
--
-- a b c : ℕ,
-- divab : a ∣ b,
-- divbc : b ∣ c
-- ⊢ a ∣ c
--    >> cases divab with d beq,
-- a b c : ℕ,
-- divbc : b ∣ c,
-- d : ℕ,
-- beq : b = a * d
-- ⊢ a ∣ c
--    >> cases divbc with e ceq,
-- a b c d : ℕ,
-- beq : b = a * d,
-- e : ℕ,
-- ceq : c = b * e
-- ⊢ a ∣ c
--    >> rw [ceq, beq],
-- ⊢ a ∣ a * d * e
--    >> use (d * e),
-- ⊢ a * d * e = a * (d * e)
--    >> ring,
-- no goals

-- 3ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divbc : b ∣ c) :
  a ∣ c :=
begin
  rcases divbc with ⟨e, rfl⟩,
  rcases divab with ⟨d, rfl⟩,
  use (d * e),
  ring,
end

-- Su desarrollo es
--
-- a b c : ℕ,
-- divab : a ∣ b,
-- divbc : b ∣ c
-- ⊢ a ∣ c
--    >> rcases divbc with ⟨e, rfl⟩,
-- a b : ℕ,
-- divab : a ∣ b,
-- e : ℕ
-- ⊢ a ∣ b * e
--    >> rcases divab with ⟨d, rfl⟩,
-- a e d : ℕ
-- ⊢ a ∣ a * d * e
--    >> use (d * e),
-- ⊢ a * d * e = a * (d * e)
--    >> ring,
-- no goals
