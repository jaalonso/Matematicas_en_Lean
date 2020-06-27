import tactic

open_locale classical

example (P Q : Prop) : (P → Q) ↔ ¬ P ∨ Q :=
begin
  split,
  { intro h1,
    by_cases h2: P,
    { right,
      apply h1,
      exact h2 },
    { left,
      exact h2 }},
  { intros h3 h4,
    cases h3,
    contradiction,
    assumption },
end
