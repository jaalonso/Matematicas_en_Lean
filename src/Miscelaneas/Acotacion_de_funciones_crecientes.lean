import data.real.basic

example
  (f : ℝ → ℝ)
  (hf : strict_mono f)
  : ∀ x ∈ set.Ioc (0 : ℝ) 1, f x ≤ f 1 :=
begin
  rintro _ ⟨-, hx⟩,
  rcases lt_or_eq_of_le hx with h | rfl,
  { exact (le_trans $ le_of_lt $ hf h) le_rfl },
  { exact le_rfl },
end
