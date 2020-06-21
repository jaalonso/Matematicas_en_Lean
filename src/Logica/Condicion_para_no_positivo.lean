import data.real.basic

-- 1ª demostración
example 
  (x : ℝ) 
  (h : ∀ ε > 0, x ≤ ε) : 
  x ≤ 0 :=
begin
  apply le_of_not_gt,
  intro hx0,
  specialize h (x/2),
  have h : x ≤ x / 2,
    { apply h,
      apply half_pos hx0},
  have : x / 2 < x,
    { apply half_lt_self hx0 },
  linarith 
end

-- 1ª demostración
example 
  (x : ℝ) 
  (h : ∀ ε > 0, x ≤ ε) : 
  x ≤ 0 :=
begin
  contrapose! h,
  use x / 2,
  split; linarith
end

