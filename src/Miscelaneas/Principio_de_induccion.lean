@[elab_as_eliminator]
lemma nat_ind
  {P : ℕ → Prop}
  (zero : P 0)
  (successor : ∀ n, P n → P (n + 1)) (n : ℕ)
  : P n :=
nat.rec zero successor n

example
  {P : ℕ → Prop}
  (z : P 0)
  (s : ∀ n, P n → P (n + 1)) (n : ℕ)
  : P n :=
begin
  with_cases { apply nat_ind },
  case zero { exact z},
  case successor : m ih { exact s m ih }
end
