import tactic

meta def tidytauto := `[tidy, tauto!]

-- 1ª demostración
example
  {α}
  (a b c : α)
  : a = b ∧ b = c ∨ ¬a = b ∧ a = c ↔ a = c :=
by tidytauto

-- 2ª demostración
example
  {α}
  (a b c : α)
  : a = b ∧ b = c ∨ ¬a = b ∧ a = c ↔ a = c :=
begin
  by_cases h : a = b;
  simp [h],
end
