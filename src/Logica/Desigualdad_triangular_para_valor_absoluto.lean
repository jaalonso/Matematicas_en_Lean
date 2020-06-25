import data.real.basic

variables {x y a b : ℝ}

namespace my_abs

-- 1ª demostración
theorem le_abs_self : x ≤ abs x :=
begin
  cases (le_or_gt 0 x) with h1 h2,
  { rw abs_of_nonneg h1 },
  { rw abs_of_neg h2,
    apply self_le_neg,
    apply le_of_lt h2 },
end

-- 2ª demostración
theorem le_abs_self_2 : x ≤ abs x :=
or.elim (le_total 0 x)
  (assume h : 0 ≤ x,
   begin rw [abs_of_nonneg h] end)
  (assume h : x ≤ 0, le_trans h $ abs_nonneg x)

theorem neg_le_abs_self : -x ≤ abs x :=
begin
  cases (le_or_gt 0 x) with h1 h2,
  { rw abs_of_nonneg h1, 
    apply neg_le_self h1 },
  { rw abs_of_neg h2 },
end

lemma aux1 
  (h1 : 0 ≤ a + b) 
  (h2 : 0 ≤ a) : 
  abs (a + b) ≤ abs a + abs b :=
decidable.by_cases
  (assume h3 : 0 ≤ b, calc
    abs (a + b) ≤ abs (a + b)   : by apply le_refl
            ... = a + b         : by rw (abs_of_nonneg h1)
            ... = abs a + b     : by rw (abs_of_nonneg h2)
            ... = abs a + abs b : by rw (abs_of_nonneg h3))
 (assume h3 : ¬ 0 ≤ b,
  have h4 : b ≤ 0, from le_of_lt (lt_of_not_ge h3),
  calc
    abs (a + b) = a + b         : by rw (abs_of_nonneg h1)
            ... = abs a + b     : by rw (abs_of_nonneg h2)
            ... ≤ abs a + 0     : add_le_add_left h4 _
            ... ≤ abs a + -b    : add_le_add_left (neg_nonneg_of_nonpos h4) _
            ... = abs a + abs b : by rw (abs_of_nonpos h4))

lemma aux2 
  (h1 : 0 ≤ a + b) : 
  abs (a + b) ≤ abs a + abs b :=
or.elim (le_total b 0)
 (assume h2 : b ≤ 0,
  have h3 : ¬ a < 0, from
    assume h4 : a < 0,
    have h5 : a + b < 0,
      begin
        have aux := add_lt_add_of_lt_of_le h4 h2,
        rwa [add_zero] at aux
      end,
    not_lt_of_ge h1 h5,
  aux1 h1 (le_of_not_gt h3))
 (assume h2 : 0 ≤ b,
  begin
    have h3 : abs (b + a) ≤ abs b + abs a,
    begin
      rw add_comm at h1,
      exact aux1 h1 h2
    end,
    rw [add_comm, add_comm (abs a)],
    exact h3
  end)

theorem abs_add : abs (x + y) ≤ abs x + abs y :=
or.elim (le_total 0 (x + y))
  (assume h2 : 0 ≤ x + y, aux2 h2)
  (assume h2 : x + y ≤ 0,
   have h3 : -x + -y = -(x + y), by rw neg_add,
   have h4 : 0 ≤ -(x + y), from neg_nonneg_of_nonpos h2,
   have h5   : 0 ≤ -x + -y, begin rw [← h3] at h4, exact h4 end,
   calc
      abs (x + y) = abs (-x + -y)   : by rw [← abs_neg, neg_add]
              ... ≤ abs (-x) + abs (-y) : aux2 h5
              ... = abs x + abs y       : by rw [abs_neg, abs_neg])

end my_abs
