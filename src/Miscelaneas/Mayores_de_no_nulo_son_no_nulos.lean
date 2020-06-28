import data.nat.basic

-- 1ª demostración
example 
  (n m : ℕ) 
  (hn : n ≠ 0) 
  (hm : n ≤ m) 
  : m ≠ 0 := 
begin
  intro h,
  simp * at *,
end

-- 2ª demostración
example 
  (n m : ℕ) 
  (hn : n ≠ 0) 
  (hm : n ≤ m) 
  : m ≠ 0 := 
λ h, by simp * at *

