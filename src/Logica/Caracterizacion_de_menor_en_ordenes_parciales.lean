import tactic

variables {α : Type*} [partial_order α]
variables a b : α

example : a < b ↔ a ≤ b ∧ a ≠ b :=
begin
  rw lt_iff_le_not_le,
  split,
    rintros ⟨h1, h2⟩,
      split,
        exact h1,
        contrapose ! h2,
        rw h2,
    rintros ⟨h3, h4⟩,
      split,
        exact h3,
        contrapose ! h4,
        apply le_antisymm h3 h4,
end
