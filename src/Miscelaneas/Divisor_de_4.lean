import tactic

-- 1ª demostración
example
  (a : ℕ)
  (h : a ∣ 4)
  (h₁ : a ≠ 1)
  (h₂ : a ≠ 2)
  : a = 4 :=
begin
  have h2 : a ≤ 4 := nat.le_of_dvd dec_trivial h,
  interval_cases a,
  { revert h, norm_num },
  { revert h₁, norm_num },
  { revert h₂, norm_num },
  { revert h, norm_num }
end

-- 1ª demostración
example
  (a : ℕ)
  (h : a ∣ 4)
  : a ≠ 1 → a ≠ 2 → a = 4 :=
begin
  have h2 : a ≤ 4 := nat.le_of_dvd dec_trivial h,
  revert h,
  interval_cases a;
  norm_num,
end
