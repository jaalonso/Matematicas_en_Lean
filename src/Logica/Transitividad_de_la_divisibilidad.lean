-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la relación de divisibilidad es transitiva. 
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

import tactic

variables {a b c : ℕ}

example 
  (divab : a ∣ b) 
  (divbc : b ∣ c) : 
  a ∣ c :=
begin
  cases divab with d beq,
  cases divbc with e ceq,
  rw [ceq, beq],
  use (d * e), 
  ring,
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

-- 2ª demostración
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


