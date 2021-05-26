-- Coprimo con potencia de primo
-- =============================

import data.nat.prime
open nat.prime

lemma not_dvd_of_coprime
  {p : ℕ}
  (h : p.prime)
  {n k : ℕ}
  (hc : n.coprime (p^(k + 1)))
  : ¬(p ∣ n) :=
λ hn, not_dvd_one h
begin
  unfold nat.coprime at hc,
  rw ← hc,
  exact nat.dvd_gcd hn ⟨p^k, rfl⟩,
end

lemma coprime_iff_not_div
  {p : ℕ}
  (h : p.prime)
  (n k : ℕ)
  : n.coprime (p^(k + 1)) ↔ ¬ (p ∣ n) :=
⟨not_dvd_of_coprime h, coprime_pow_of_not_dvd h⟩
