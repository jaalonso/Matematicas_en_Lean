import data.real.basic

variables a b c : ℝ

example : min (min a b) c = min a (min b c) :=
begin
  apply le_antisymm,
  { show min (min a b) c ≤ min a (min b c),
    apply le_min,
    { show min (min a b) c ≤ a,
      have h1 : min (min a b) c ≤ min a b, 
        { apply min_le_left },
      have h2 : min a b ≤ a,
        { apply min_le_left },
      apply le_trans h1 h2 },
    { show min (min a b) c ≤ min b c,
      have h3 : min (min a b) c ≤ b,
        { have h4 : min (min a b) c ≤  min a b,
            { apply min_le_left },
          have h5 : min a b ≤ b, 
            { apply min_le_right },
          apply le_trans h4 h5 },
      have h6 : min (min a b) c ≤ c,
        { apply min_le_right },
    apply le_min h3 h6 } },
  { show min a (min b c) ≤ min (min a b) c,
    apply le_min,
  sorry


