-- Ref: The conversion tactic mode https://bit.ly/3kqif1T

import tactic

example (a b c : ℕ) : a * (b * c) = a * (c * b) :=
begin
  conv
  begin          -- | a * (b * c) = a * (c * b)
    to_lhs,      -- | a * (b * c)
    congr,       -- 2 goals : | a and | b * c
    skip,        -- | b * c
    rw mul_comm, -- | c * b
  end
end

example (a b c : ℕ) : a * (b * c) = a * (c * b) :=
begin
  conv in (b*c)
  begin          -- | b * c
    rw mul_comm, -- | c * b
  end,
end

example (a b c : ℕ) : a * (b * c) = a * (c * b) :=
by conv in (b*c) { rw mul_comm }

example (a b c : ℕ) : a + (b * c) = a + (c * b) :=
by conv in (_ * c) { rw mul_comm }

example (a b c : ℕ) : (b * c) * (b * c) * (b * c) = (b * c) * (c * b)  * (c * b):=
by conv { for (b * c) [2, 3] { rw mul_comm } }

example : (λ x : ℕ, 0 + x) = (λ x, x) :=
begin
  conv
  begin           -- | (λ (x : ℕ), 0 + x) = λ (x : ℕ), x
    to_lhs,       -- | λ (x : ℕ), 0 + x
    funext,       -- | 0 + x
    rw zero_add,  -- | x
  end
end

example : (λ x : ℕ, 0+x) = (λ x, x) :=
by funext ; rw zero_add
