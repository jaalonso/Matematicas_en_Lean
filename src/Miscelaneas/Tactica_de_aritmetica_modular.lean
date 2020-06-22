import tactic

import data.nat.basic
import data.zmod.basic

example 
  (a b c : zmod 5) 
  (ha : a = 1) 
  (hb : b = 3)
  (hc : c = 4) : 
  (a^2 + (b + 2*c)^3) = 2 :=
begin
  rw [ha, hb, hc], 
  ring,
end
