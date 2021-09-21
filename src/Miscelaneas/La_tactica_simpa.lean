import tactic

-- Con simpa
example
  (n : ℕ)
  (h : n + 1 - 1 ≠ 0)
  : n + 1 ≠ 1 :=
by simpa using h

-- Sin simpa
example
  (n : ℕ)
  (h : n + 1 - 1 ≠ 0)
  : n + 1 ≠ 1 :=
begin
  simp at ⊢ h,
  exact h,
end
