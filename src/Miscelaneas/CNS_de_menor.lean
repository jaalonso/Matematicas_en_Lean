import tactic

lemma sub_diff
  (m m' : ℕ)
  (h : m < m')
  : ∃ s : ℕ, 0 < s ∧ m' = m + s :=
begin
  use m' - m,
  split,
  { omega, },
  { exact (nat.add_sub_of_le (le_of_lt h)).symm }
end

-- 2ª demostración
lemma nat.exists_eq_add_of_lt'
  (m m' : ℕ)
  (h : m < m')
  : ∃ s : ℕ, 0 < s ∧ m' = m + s :=
let ⟨k, hk⟩ := nat.exists_eq_add_of_lt h
in ⟨k.succ, k.zero_lt_succ, hk⟩
