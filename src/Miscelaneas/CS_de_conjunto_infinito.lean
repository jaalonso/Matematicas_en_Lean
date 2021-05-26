import data.set.finite
import data.set.function

open function set

variable (α : Type)

lemma useful
  {X : set α}
  (h: ∃ (f : ℕ → α), injective f ∧ range f ⊆ X)
  : X.infinite :=
begin
  rcases h with ⟨f, hfi, hfX⟩,
  apply infinite_of_injective_forall_mem hfi,
  exact range_subset_iff.mp hfX,
end
