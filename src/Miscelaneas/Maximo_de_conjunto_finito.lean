import data.set.finite

namespace hidden

open_locale classical

lemma foo
  (s : set ℕ)
  (hs : s.finite)
  (hsn : s.nonempty)
  : ∃ k, ∀ n ∈ s, n ≤ k :=
begin
  use hs.to_finset.max' (by simpa),
  intros n hn,
  rw ←@set.finite.mem_to_finset _ _ hs at hn,
  exact finset.le_max' _ _ hn,
end

noncomputable
def max (s : set ℕ) (hs : s.finite) :=
if hsn : s.nonempty then
  nat.find $ foo s hs hsn
else
  0

lemma max_spec
  (s : set ℕ)
  (hs : s.finite)
  (n : ℕ)
  (hn : n ∈ s)
  : n ≤ max s hs :=
begin
  by_cases hsn : s.nonempty,
  { unfold max,
    rw dif_pos hsn,
    exact nat.find_spec (foo s hs hsn) _ hn },
  { rw set.not_nonempty_iff_eq_empty at hsn,
    rw hsn at hn,
    cases hn }
end

end hidden
