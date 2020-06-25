import tactic

example (n m k : ℕ) : n * (m - k) = n * m - n * k :=
begin
  library_search,
  sorry
end

-- Al colocar el cursor sobre library_search escribe
--    Try this: exact nat.mul_sub_left_distrib n m k

example (n m k : ℕ) : n * (m - k) = n * m - n * k :=
begin
  exact nat.mul_sub_left_distrib n m k,
end

-- Ver la documentación en https://bit.ly/3dEmh0l


