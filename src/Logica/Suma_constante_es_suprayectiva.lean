import data.real.basic

open function

-- 1ª demostración
example {c : ℝ} : surjective (λ x, x + c) :=
begin
  intro x,
  use x - c,
  dsimp, 
  ring
end

-- 2ª demostración
example {c : ℝ} : surjective (λ x, x + c) :=
begin
  intro x,
  use x - c,
  change (x - c) + c = x,
  ring
end
