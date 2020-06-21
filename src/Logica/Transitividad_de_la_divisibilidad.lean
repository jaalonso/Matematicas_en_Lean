import tactic

variables {a b c : ℕ}

-- 1ª demostración
example 
  (divab : a ∣ b) 
  (divbc : b ∣ c) : 
  a ∣ c :=
begin
  cases divab with d beq,
  cases divbc with e ceq,
  rw [ceq, beq],
  use (d * e), 
  ring
end

-- 2ª demostración
example 
  (divab : a ∣ b) 
  (divbc : b ∣ c) : 
  a ∣ c :=
begin
  rcases divbc with ⟨e, rfl⟩,
  rcases divab with ⟨d, rfl⟩,
  use (d * e), 
  ring
end

