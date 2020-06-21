import tactic

variables {a b c : ℕ}

-- 1ª demostración
example 
  (divab : a ∣ b) 
  (divac : a ∣ c) : 
  a ∣ (b + c) :=
begin
  cases divab with d beq,
  cases divac with e ceq,
  rw [ceq, beq],
  use (d + e), 
  ring
end

-- 2ª demostración
example 
  (divab : a ∣ b) 
  (divac : a ∣ c) : 
  a ∣ (b + c) :=
begin
  rcases divab with ⟨d, rfl⟩,
  rcases divac with ⟨e, rfl⟩,
  use (d + e), 
  ring
end
