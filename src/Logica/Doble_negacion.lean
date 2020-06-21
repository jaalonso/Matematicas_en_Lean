import tactic

open_locale classical

variable (Q : Prop)

-- BEGIN
example (h : ¬ ¬ Q) : Q :=
begin 
  by_contradiction h1,
  exact (h h1)
end

example (h : Q) : ¬ ¬ Q :=
begin
  intro h1,
  exact (h1 h)
end
