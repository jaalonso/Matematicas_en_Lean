import tactic

variables {α : Type*} [preorder α]
variables a b c : α

example : ¬ a < a :=
begin
  rw lt_iff_le_not_le,
  rintros ⟨h1, h2⟩,
  apply h2 h1,
end

example : a < b → b < c → a < c :=
begin
  simp only [lt_iff_le_not_le],
  rintros ⟨h1, h2⟩ ⟨h3, h4⟩,
  split,
    apply le_trans h1 h3,
    contrapose ! h4,
    apply le_trans h4 h1,
end
