-- El comando refine
-- =================

import tactic

example
  {A}
  (Q : Prop)
  (P P₀ : A → Prop)
  (h : Q → ∃ a : A, P₀ a)
  (q : Q)
  (H : ∀ a : A, P₀ a → P a)
  : (∃ a : A, P a) :=
begin
  rcases h q with ⟨a, h⟩,
  refine ⟨a, _⟩,
  exact H _ h,
end

example
  {A}
  (Q : Prop)
  (P P₀ : A → Prop)
  (h : Q → ∃ a : A, P₀ a)
  (q : Q)
  (H : ∀ a : A, P₀ a → P a)
  : (∃ a : A, P a) :=
Exists.imp H (h q)
