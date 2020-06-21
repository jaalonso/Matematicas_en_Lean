import data.real.basic

variables a b c d : ℝ

example : (c * b) * a = b * (a * c) :=
by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
by ring

example : (a + b) * (a - b) = a^2 - b^2 :=
by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) :
  c = 2 * a * d :=
begin
  rw [hyp, hyp'],
  ring
end

-- Notas:
-- + Nota 1: La táctica ring se importa automáticamente con
--      import data.real.basic. 
-- + Nota 2: La táctica ring se importa con
--      import tactic
