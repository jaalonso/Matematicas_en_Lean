import data.nat.gcd

open nat

-- 1ª demostración
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) :
  m ∣ n ∧ ¬ n ∣ m :=
begin
  cases h with h₀ h₁,
  split,
    exact h₀,
  contrapose! h₁,
  apply dvd_antisymm h₀ h₁
end

-- 2ª demostración
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) :
  m ∣ n ∧ ¬ n ∣ m :=
begin
  rcases h with ⟨h₀, h₁⟩,
  split,
    exact h₀,
  contrapose! h₁,
  apply dvd_antisymm h₀ h₁
end
