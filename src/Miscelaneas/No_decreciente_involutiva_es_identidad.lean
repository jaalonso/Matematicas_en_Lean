import data.real.basic

def non_decreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

-- 1ª demostración
example 
  (f : ℝ → ℝ) 
  (h : non_decreasing f) 
  (h' : ∀ x, f (f x) = x) : 
  ∀ x, f x = x :=
begin
  intro x,
  specialize h' x,
  unfold non_decreasing at h,
  cases le_total (f x) x with,
  { specialize h (f x) x h_1,
    rw h' at h,
    exact le_antisymm h_1 h },
  { specialize h x (f x) h_1,
    rw h' at h,
    exact le_antisymm h h_1 }
end

-- 2ª demostración
example 
  (f : ℝ → ℝ) 
  (h : non_decreasing f) 
  (h' : ∀ x, f (f x) = x) : 
  ∀ x, f x = x :=
begin
  intro x,
  specialize h' x,
  cases le_total x (f x);
  linarith [h _ _ h_1]
end
