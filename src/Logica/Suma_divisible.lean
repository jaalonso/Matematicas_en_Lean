-- ---------------------------------------------------------------------
-- Ejercicio 1. Demostrar que si a es un divisor de b y de c, tambien lo
-- es de b + c.
-- ----------------------------------------------------------------------

import tactic

variables {a b c : ℕ}

-- 1ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divac : a ∣ c)
  : a ∣ (b + c) :=
begin
  rcases divab with ⟨d, beq : b = a * d⟩,
  rcases divac with ⟨e, ceq: c = a * e⟩,
  have h1 : b + c = a * (d + e),
    calc b + c
         = (a * d) + c       : congr_arg (+ c) beq
     ... = (a * d) + (a * e) : congr_arg ((+) (a * d)) ceq
     ... = a * (d + e)       : by rw ← mul_add,
  show a ∣ (b + c),
    by exact dvd.intro (d + e) (eq.symm h1),
end

-- 2ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divac : a ∣ c)
  : a ∣ (b + c) :=
begin
  rcases divab with ⟨d, beq : b = a * d⟩,
  rcases divac with ⟨e, ceq: c = a * e⟩,
  have h1 : b + c = a * (d + e), by linarith,
  show a ∣ (b + c),
    by exact dvd.intro (d + e) (eq.symm h1),
end

-- 3ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divac : a ∣ c)
  : a ∣ (b + c) :=
begin
  rcases divab with ⟨d, beq : b = a * d⟩,
  rcases divac with ⟨e, ceq: c = a * e⟩,
  show a ∣ (b + c),
    by exact dvd.intro (d + e) (by linarith),
end

-- 4ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divac : a ∣ c)
  : a ∣ (b + c) :=
begin
  cases divab with d beq,
  cases divac with e ceq,
  rw [ceq, beq],
  use (d + e),
  ring
end

-- Su desarrollo es
--
-- a b c : ℕ,
-- divab : a ∣ b,
-- divac : a ∣ c
-- ⊢ a ∣ b + c
--    >> cases divab with d beq,
-- a b c : ℕ,
-- divac : a ∣ c,
-- d : ℕ,
-- beq : b = a * d
-- ⊢ a ∣ b + c
--    >> cases divac with e ceq,
-- a b c d : ℕ,
-- beq : b = a * d,
-- e : ℕ,
-- ceq : c = a * e
-- ⊢ a ∣ b + c
--    >> rw [ceq, beq],
-- ⊢ a ∣ a * d + a * e
--    >> use (d + e),
-- ⊢ a * d + a * e = a * (d + e)
--    >> ring,
-- no goals

-- 5ª demostración
-- ===============

example
  (divab : a ∣ b)
  (divac : a ∣ c)
  : a ∣ (b + c) :=
begin
  rcases divab with ⟨d, rfl⟩,
  rcases divac with ⟨e, rfl⟩,
  use (d + e),
  ring,
end

-- Su desarrollo es
--
-- a b c : ℕ,
-- divab : a ∣ b,
-- divac : a ∣ c
-- ⊢ a ∣ b + c
--    >> rcases divab with ⟨d, rfl⟩,
-- a c : ℕ,
-- divac : a ∣ c,
-- d : ℕ
-- ⊢ a ∣ a * d + c
--    >> rcases divac with ⟨e, rfl⟩,
-- ⊢ a ∣ a * d + a * e
--    >> use (d + e),
-- ⊢ a * d + a * e = a * (d + e)
--    >> ring
-- no goals
