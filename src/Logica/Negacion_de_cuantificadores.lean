import tactic

variables {α : Type*} (P : α → Prop)

example 
  (h : ¬ ∃ x, P x) : 
  ∀ x, ¬ P x :=
begin
  intros x h1,
  apply h,
  existsi x,
  exact h1
end

example 
  (h : ∀ x, ¬ P x) : 
  ¬ ∃ x, P x :=
begin
  intro h1,
  cases h1 with x hx,
  specialize h x,
  apply h hx
end

open_locale classical

example 
  (h : ¬ ∀ x, P x) : 
  ∃ x, ¬ P x :=
begin
  by_contradiction h',
  apply h,
  intro x,
  show P x,
  by_contradiction h'',
  exact h' ⟨x, h''⟩
end

example 
  (h : ∃ x, ¬ P x) : 
  ¬ ∀ x, P x :=
begin
  intro h1,
  cases h with x hx,
  apply hx,
  exact (h1 x)
end
