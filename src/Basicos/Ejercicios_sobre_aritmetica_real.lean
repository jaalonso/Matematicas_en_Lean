import data.real.basic

example (a b c : ℝ) : (c * b) * a = b * (a * c) :=
begin
  rw mul_comm c b,
  rw mul_assoc,
  rw mul_comm c a,
end

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  rw ←mul_assoc,
  rw mul_comm a b,
  rw mul_assoc,
end
