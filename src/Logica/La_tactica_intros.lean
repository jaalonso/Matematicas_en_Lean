import data.real.basic tactic

lemma my_lemma : ∀ {x y ε : ℝ},
  0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
begin
  intros x y ε epos ele1 xlt ylt,
  by_cases (abs x = 0),
  { calc abs (x * y) = abs x * abs y : by apply abs_mul
                 ... = 0 * abs y     : by rw h
                 ... = 0             : by apply zero_mul
                 ... < ε             : by apply epos
  },
  { have h1 : 0 < abs x,
      { have h2 : 0 ≤ abs x,
          apply abs_nonneg,
        exact lt_of_le_of_ne h2 (ne.symm h)
      },
    calc
      abs (x * y) = abs x * abs y : by rw abs_mul
              ... < abs x * ε     : by apply (mul_lt_mul_left h1).mpr ylt
              ... < ε * ε         : by apply (mul_lt_mul_right epos).mpr xlt
              ... ≤ 1 * ε         : by apply (mul_le_mul_right epos).mpr ele1
              ... = ε             : by rw [one_mul]
  },
end
