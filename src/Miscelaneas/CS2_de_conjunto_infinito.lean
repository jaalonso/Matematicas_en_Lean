import tactic

open set

lemma useful2
  (Y : set ℕ)
  : (∀ (x : ℕ), ∃ (y : ℕ), x ≤ y ∧ y ∈ Y) → Y.infinite :=
begin
  intros h hY,
  obtain ⟨N, hN⟩ : bdd_above Y := finite.bdd_above hY,
  obtain ⟨y, hNy, hyY⟩ : ∃ (y : ℕ), N + 1 ≤ y ∧ y ∈ Y := h (N + 1),
  specialize hN hyY,
  linarith,
end
