-- ---------------------------------------------------------------------
-- Ejercicio. Sean a, b y c números reales. Demostrar que
--    min a b + c = min (a + c) (b + c)
-- ----------------------------------------------------------------------

import data.real.basic

variables a b c : ℝ

-- 1ª demostración
-- ===============

lemma aux1a :
  min a b + c ≤ min (a + c) (b + c) :=
begin
  have h1 : min a b  ≤ a :=
    min_le_left a b,
  have h2 : min a b + c ≤ a + c :=
    add_le_add_right h1 c,
  have h3 : min a b  ≤ b :=
    min_le_right a b,
  have h4 : min a b + c ≤ b + c :=
    add_le_add_right h3 c,
  show min a b + c ≤ min (a + c) (b + c),
    by exact le_min h2 h4,
end

lemma aux2a :
  min (a + c) (b + c) ≤ min a b + c :=
begin
  have h1 : min (a + c) (b + c) + -c ≤ min a b,
  { calc min (a + c) (b + c) + -c
         ≤ min (a + c + -c) (b + c + -c) : aux1a (a + c) (b + c) (-c)
     ... = min a b                       : by ring_nf },
  show min (a + c) (b + c) ≤ min a b + c,
    by exact add_neg_le_iff_le_add.mp h1,
end

example :
  min a b + c = min (a + c) (b + c) :=
begin
  apply le_antisymm,
  { exact aux1a a b c, },
  { exact aux2a a b c, },
end

-- 2ª demostración
-- ===============

lemma aux1b :
  min a b + c ≤ min (a + c) (b + c) :=
begin
  apply le_min,
  { apply add_le_add_right,
    exact min_le_left a b, },
  { apply add_le_add_right,
    exact min_le_right a b, },
end

lemma aux2b :
  min (a + c) (b + c) ≤ min a b + c :=
begin
  have h1 : min (a + c) (b + c) + -c ≤ min a b,
  { calc min (a + c) (b + c) + -c
         ≤ min (a + c + -c) (b + c + -c) : aux1b (a + c) (b + c) (-c)
     ... = min a b                       : by ring_nf },
  exact add_neg_le_iff_le_add.mp h1,
end

example :
  min a b + c = min (a + c) (b + c) :=
begin
  apply le_antisymm,
  { exact aux1b a b c, },
  { exact aux2b a b c, },
end

-- 3ª demostración
-- ===============

lemma aux1c :
  min a b + c ≤ min (a + c) (b + c) :=
le_min (add_le_add_right (min_le_left a b) c)
       (add_le_add_right (min_le_right a b) c)

lemma aux2c :
  min (a + c) (b + c) ≤ min a b + c :=
begin
  have h1 : min (a + c) (b + c) + -c ≤ min a b,
  { calc min (a + c) (b + c) + -c
         ≤ min (a + c + -c) (b + c + -c) : aux1c (a + c) (b + c) (-c)
     ... = min a b                       : by ring_nf },
  exact add_neg_le_iff_le_add.mp h1,
end

example :
  min a b + c = min (a + c) (b + c) :=
le_antisymm (aux1b a b c) (aux2b a b c)

-- 4ª demostración
-- ===============

example : min a b + c = min (a + c) (b + c) :=
begin
  by_cases (a ≤ b),
  { have h1 : a + c ≤ b + c,
      apply add_le_add_right h,
    calc min a b + c = a + c               : by simp [min_eq_left h]
                 ... = min (a + c) (b + c) : by simp [min_eq_left h1]},
  { have h2: b ≤ a,
      linarith,
    have h3 : b + c ≤ a + c,
      { exact add_le_add_right h2 c },
    calc min a b + c = b + c               : by simp [min_eq_right h2]
                 ... = min (a + c) (b + c) : by simp [min_eq_right h3]},
end

-- 5ª demostración
-- ===============

example : min a b + c = min (a + c) (b + c) :=
(min_add_add_right a b c).symm
