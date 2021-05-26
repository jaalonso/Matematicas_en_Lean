import order.basic

lemma aux
  {P : ℕ → ℕ → Prop}
  (h : ∀ n, ∀ N, ∃ k > N, P n k)
  : ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, P n (φ n) :=
begin
  choose u hu hu' using h,
  use (λ n, nat.rec_on n (u 0 0) (λ n v, u (n+1) v) : ℕ → ℕ),
  split,
  { apply strict_mono.nat,
    intro n,
    apply hu },
  { intros n,
    cases n ; simp [hu'] },
end

lemma aux'
  {P : ℕ → ℕ → Prop}
  (h : ∀ n, ∀ N, ∃ k ≥ N, P n k)
  : ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, P n (φ n) :=
begin
  apply aux,
  intros n N,
  rcases h n (N+1) with ⟨k, hk, hk'⟩,
  use k; tauto
end

lemma aux''
  {P : ℕ → ℕ → Prop}
  (h : ∀ n, ∃ N, ∀ k ≥ N, P n k)
  : ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, P n (φ n) :=
begin
  apply aux',
  intros n N,
  cases h n with N₀ hN₀,
  exact ⟨max N N₀, le_max_left _ _, hN₀ _ $ le_max_right _ _⟩,
end
