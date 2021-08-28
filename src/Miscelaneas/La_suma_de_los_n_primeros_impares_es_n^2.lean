import data.finset
import algebra.big_operators
import tactic.ring
open nat

set_option pp.structure_projections false

variable (n : ℕ)

def impar (n : ℕ) := 2 * n + 1

-- (finset.range n) es el conjunto finito {0,1,2,...,n-1}. Por ejemplo,
--    #eval (finset.range 3)                  -- => {0, 1, 2}
--    #eval finset.sum (finset.range 3) impar -- => 9

-- 1ª demostración
example :
  finset.sum (finset.range n) impar = n ^ 2 :=
begin
  induction n with d hd,
    refl,
  rw finset.sum_range_succ,
  rw hd,
  change d ^ 2 + (2 * d + 1) = (d + 1) ^ 2,
  ring,
end

-- 2ª demostración
example :
  finset.sum (finset.range n) impar = n ^ 2 :=
begin
  induction n with m HI,
  { calc finset.sum (finset.range 0) impar
          = 0
            : by simp
     ...  = 0 ^ 2
            : rfl, },
  { calc finset.sum (finset.range (succ m)) impar
         = finset.sum (finset.range m) impar + impar m
           : finset.sum_range_succ impar m
     ... = m ^ 2 + impar m
           : congr_arg2 (+) HI rfl
     ... = m ^ 2 + 2 * m + 1
           : rfl
     ... = (m + 1) ^ 2
           : by ring_nf
     ... = succ m ^ 2
           : rfl },
end
