import data.real.basic

variables {x y : ℝ}

namespace my_abs

theorem lt_abs : x < abs y ↔ x < y ∨ x < -y :=
begin
  unfold abs,
  exact lt_max_iff,
end

theorem abs_lt : abs x < y ↔ - y < x ∧ x < y :=
begin
  unfold abs,
  exact abs_lt,
end

end my_abs
