import data.real.basic

example :
  ¬ ∀ {f : ℝ → ℝ}, monotone f → ∀ {a b}, f a ≤ f b → a ≤ b :=
begin
  intro h,
  let f := λ x : ℝ, (0 : ℝ),
  have monof : monotone f,
    { assume x y h,
      linarith },
  have h' : f 1 ≤ f 0,
    from le_refl _,
  have : 1 ≤ 0,
    sorry
end
