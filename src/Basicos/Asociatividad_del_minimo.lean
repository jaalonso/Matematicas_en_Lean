import data.real.basic tactic

variables a b c : ℝ

lemma aux1 : min (min a b) c ≤ min a (min b c) :=
begin
  apply le_min,
  { show min (min a b) c ≤ a,
      calc min (min a b) c ≤ min a b : by apply min_le_left
                      ...  ≤ a       : by apply min_le_left },
  { show min (min a b) c ≤ min b c,
    apply le_min,
    { show min (min a b) c ≤ b,
        calc  min (min a b) c ≤  min a b : by apply min_le_left
                          ... ≤ b        : by apply min_le_right },
    { show min (min a b) c ≤ c,
      { apply min_le_right }}},
end

example : min (min a b) c = min a (min b c) :=
begin
  apply le_antisymm,
  { show min (min a b) c ≤ min a (min b c),
      by exact aux1 a b c },
  { show min a (min b c) ≤ min (min a b) c,
      calc min a (min b c) = min (min b c) a : by apply min_comm
                       ... = min (min c b) a : by {congr' 1, apply min_comm}
                       ... ≤ min c (min b a) : by apply aux1
                       ... = min c (min a b) : by {congr' 1, apply min_comm}
                       ... = min (min a b) c : by apply min_comm
  },
end
