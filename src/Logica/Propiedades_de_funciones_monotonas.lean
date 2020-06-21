import data.real.basic

variables (f : ℝ → ℝ) (a b : ℝ)

example 
  (h : monotone f) 
  (h' : f a < f b) : 
  a < b :=
begin
  apply lt_of_not_ge,
  intro hab,
  have : f a ≥ f b,
    from h hab,
  linarith
end

example 
  (h : a ≤ b) 
  (h' : f b < f a) : 
  ¬ monotone f :=
begin
  intro h1,
  have : f a ≤ f b,
    from h1 h,
  linarith
end
