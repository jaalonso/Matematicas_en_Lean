import data.real.basic

def S := {x : real | x*x <= 2}

-- 1ª demostración
example : (0 : ℝ) ∈ S :=
begin
  dsimp [S],
  norm_num,
end

-- 2ª demostración
example : (0 : ℝ) ∈ S :=
begin
  change (0 : ℝ) * 0 ≤ 2,
  norm_num,
end

-- 3ª demostración
example : (0 : ℝ) ∈ S :=
begin
  unfold S,
  rw set.mem_set_of_eq,
  norm_num,
end
