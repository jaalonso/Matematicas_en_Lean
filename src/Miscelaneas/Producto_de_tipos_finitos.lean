-- Producto de tipos finitos
-- =========================

import data.fintype.card

example
  (A B : Type*)
  [fintype A]
  [fintype B]
  : fintype (A × B) :=
by apply_instance

universe u

def is_example (a : Type u) : Prop :=
∃ (Q : Type u) [fintype Q], Q = a

variables (a b : Type u)

lemma is_example_prod :
  is_example a → is_example b → is_example (a × b) :=
begin
  rintros ⟨Q, hQ, f⟩,
  rintros ⟨Q', hQ', f'⟩,
  resetI,
  refine ⟨Q × Q', infer_instance, _⟩,
  congr; assumption,
end

lemma is_example_prod2 :
  is_example a → is_example b → is_example (a × b) :=
begin
  rintros ⟨Q, hQ, f⟩,
  rintros ⟨Q', hQ', f'⟩,
  resetI,
  refine ⟨Q × Q', _, _⟩,
  apply_instance,
  congr; assumption,
end
