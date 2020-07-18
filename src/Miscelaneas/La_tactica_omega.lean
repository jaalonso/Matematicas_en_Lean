import tactic

-- 1ª demostración
example (n : ℕ ): ¬ n = 0 → n ≥ 1 :=
by omega

-- 2ª demostración
example (n : ℕ ): ¬ n = 0 → n ≥ 1 := 
nat.pos_of_ne_zero

-- 3ª demostración
example (n : ℕ ): ¬ n = 0 → n ≥ 1 :=
begin
  intro h,
  induction HI : n ,
  { contrapose! h, 
    { assumption }},
  -- suggest,
  { exact inf_eq_left.mp rfl },
end
