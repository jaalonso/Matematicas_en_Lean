import data.real.basic

noncomputable def star : ℝ → ℝ → ℝ
| x y := x + y - ⌊ x + y ⌋

lemma star_closed {a b : ℝ}
  (ha : a ∈ set.Ico (0:ℝ) 1) (hb : b ∈ set.Ico (0:ℝ) 1) :
  (star a b) ∈ set.Ico (0:ℝ) 1 :=
begin
  unfold star,
  split,
  { -- try { library_search }, -- library_search fails
    suggest, -- but suggest works: Try this: exact fract_nonneg (a + b)
    sorry },
  { try { library_search },
    suggest,
    sorry },
end
