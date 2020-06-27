import tactic

-- 1ª demostración
-- ===============

example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  cases classical.em P,
  { assumption },
  { contradiction },
end

-- 2ª demostración
-- ===============

open classical

example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  cases em P,
  { assumption },
  { contradiction },
end

-- 2ª demostración
-- ===============

open_locale classical

example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  by_cases h' : P,
  { assumption },
  { contradiction }
end
