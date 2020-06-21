import data.real.basic

variables a b c : ℝ

lemma aux1 : min a b + c ≤ min (a + c) (b + c) :=
begin
  apply le_min,
  { show min a b + c ≤ a + c,
    { apply add_le_add,
      { apply min_le_left },
      apply le_refl 
    }, 
  },
  { show min a b + c ≤ b + c,
    { apply add_le_add,
      { apply min_le_right },
      apply le_refl 
    }, 
  }
end

lemma aux2 : min (a + c) (b + c) ≤ min a b + c :=
sorry

#check add_neg_cancel_right

example : min a b + c = min (a + c) (b + c) :=
begin
  apply le_antisymm,
    apply aux1,
  apply aux2,
end

