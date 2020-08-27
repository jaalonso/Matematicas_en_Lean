import tactic

example {r s : ℕ} : {n | n ≤ r} ⊆ {n | n ≤ r + s} :=
begin
  intros n hn,
  simp at hn,
  apply le_trans hn,
  exact nat.le.intro rfl,
end
