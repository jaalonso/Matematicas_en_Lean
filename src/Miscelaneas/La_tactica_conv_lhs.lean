import data.real.basic
import tactic

example
  {x : ℝ}
  (hx : x = 1)
  : x + 1 < 2 + x :=
begin
  conv_lhs {rw hx},
  linarith,
end
