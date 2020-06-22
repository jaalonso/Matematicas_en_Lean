import data.real.basic

example 
  (x y : ℝ) : 
  abs (x + 3) < 5 → -8 < x ∧ x < 2 :=
begin
  rw abs_lt,
  intro h,
  split; linarith
end

-- Lemas usados
-- ============

#check abs_lt -- | abs a < b ↔ -b < a ∧ a < b
