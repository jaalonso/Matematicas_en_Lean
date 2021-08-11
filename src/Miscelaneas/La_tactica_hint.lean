import tactic

-- example {P Q : Prop} (p : P) (h : P → Q) : Q :=
-- begin
--   by hint,
--   sorry,
-- end

example {P Q : Prop} (p : P) (h : P → Q) : Q :=
by tauto

example {P Q : Prop} (p : P) (h : P → Q) : Q :=
by finish

example {P Q : Prop} (p : P) (h : P → Q) : Q :=
by solve_by_elim

-- Al colocar el cursor sobre hint escribe
--    the following tactics solve the goal:
--    ----
--    Try this: tauto
--    Try this: finish
--    Try this: solve_by_elim

-- Ver la documentación en https://bit.ly/2Z56ceN
