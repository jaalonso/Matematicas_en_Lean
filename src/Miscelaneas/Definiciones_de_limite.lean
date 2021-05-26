-- Definiciones de límite
-- ======================

import topology.instances.real

notation `|` x `|` := abs x

definition is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε

open filter

open_locale topological_space

lemma is_limit_iff_tendsto
  (a : ℕ → ℝ)
  (l : ℝ)
  : is_limit a l ↔ tendsto a at_top (𝓝 l) :=
begin
  split,
  { intros h X hX,
    rw mem_nhds_iff_exists_Ioo_subset at hX,
    rcases hX with ⟨x, y, ⟨hxl, hly⟩, h2⟩,
    set ε := min (l - x) (y - l) with hε,
    have hε_pos : 0 < ε := lt_min (by linarith) (by linarith),
    obtain ⟨N, hN⟩ := h ε hε_pos,
    rw [mem_map, mem_at_top_sets],
    use N,
    intros n hn,
    specialize hN n hn,
    apply h2,
    rw abs_lt at hN,
    cases hN,
    have hε1 : ε ≤ l - x := min_le_left _ _,
    have hε2 : ε ≤ y - l := min_le_right _ _,
    split;
    linarith },
  { intros h ε hε,
    rw tendsto_nhds at h,
    specialize h (set.Ioo (l - ε) (l + ε)) (is_open_Ioo) ⟨by linarith, by linarith⟩,
    rw mem_at_top_sets at h,
    rcases h with ⟨N, hN⟩,
    use N,
    intros n hn,
    obtain ⟨h1, h2⟩ := hN n hn,
    rw abs_lt,
    split; linarith },
end

example
  (a b : ℕ → ℝ)
  (l m : ℝ)
  : is_limit a l → is_limit b m → is_limit (λ n, a n + b n) (l + m) :=
begin
  simp only [is_limit_iff_tendsto],
  exact tendsto.add,
end

example
  (a b : ℕ → ℝ)
  (l m : ℝ)
  : is_limit a l → is_limit b m → is_limit (λ n, a n * b n) (l * m) :=
begin
  simp only [is_limit_iff_tendsto],
  exact tendsto.mul,
end
