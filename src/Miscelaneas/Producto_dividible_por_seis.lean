-- Producto dividible por seis
-- ===========================

import tactic

lemma six_div
  (n : ℤ)
  : 6 ∣ (n*(n-1)*(2*n-1)) :=
begin
  apply int.induction_on n; clear n,
  { simp },
  { rintro i ⟨m, hn⟩,
    use m+i^2,
    rw [mul_add (6 : ℤ), ← hn],
    ring },
  { rintro i ⟨m, hn⟩,
    use m-(i+1)^2,
    rw [mul_sub (6 : ℤ), ← hn],
    ring, },
end
