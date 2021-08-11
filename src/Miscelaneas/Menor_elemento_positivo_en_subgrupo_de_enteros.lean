-- Menor_elemento_positivo_en_subgrupo_de_enteros.lean
-- Menor elemento positivo en subgrupo de enteros.
-- José A. Alonso Jiménez
-- Sevilla, 13 de julio de 2021
-- ---------------------------------------------------------------------

import tactic
import data.int.least_greatest

-- 1ª demostración
example
  (H : set ℤ)
  (x : ℤ)
  (hx : x ∈ H)
  (xpos : 0 < x)
  : ∃! (b : ℤ), 0 < b ∧ b ∈ H ∧ (∀ (c ∈ H), 0 < c → b ≤ c) :=
begin
  set bs : set ℤ := {b : ℤ | b ∈ H ∧ 0 < b} with hbs,
  classical,
  have h1 : ∃ b, b ∈ bs ∧ ∀ z, z ∈ bs → b ≤ z,
  { apply int.exists_least_of_bdd,
    { use 0,
      intros z hz,
      apply le_of_lt,
      exact and.right hz, },
    { use x,
      split,
      { exact hx, },
      { exact xpos, }}},
  rcases h1 with ⟨lb, hlb, hlb'⟩,
  simp only [set.mem_set_of_eq] at hlb,
  simp only [and_imp, set.mem_set_of_eq] at hlb',
  use lb,
  dsimp,
  split,
  { split,
    { exact hlb.2, },
    { split,
      { exact hlb.1, },
      { exact hlb', }}},
  { simp only [and_imp],
    intros c cpos hc IH,
    apply le_antisymm,
    { exact IH lb hlb.1 hlb.2, },
    { exact hlb' c hc cpos, }},
end

-- 2ª demostración
example
  (H : set ℤ)
  (x : ℤ)
  (hx : x ∈ H)
  (xpos : 0 < x)
  : ∃! (b : ℤ), 0 < b ∧ b ∈ H ∧ (∀ (c ∈ H), 0 < c → b ≤ c) :=
begin
  set bs : set ℤ := {b : ℤ | b ∈ H ∧ 0 < b} with hbs,
  classical,
  have h1 : ∃ b, b ∈ bs ∧ ∀ z, z ∈ bs → b ≤ z,
  { apply int.exists_least_of_bdd,
    { use 0,
      intros z hz,
      exact le_of_lt (and.right hz), },
    { use x,
      exact and.intro hx xpos, }},
  rcases h1 with ⟨lb, hlb, hlb'⟩,
  simp only [set.mem_set_of_eq] at hlb,
  simp only [and_imp, set.mem_set_of_eq] at hlb',
  use lb,
  dsimp,
  split,
  { split,
    { exact hlb.2, },
    { split,
      { exact hlb.1, },
      { exact hlb', }}},
  { simp only [and_imp],
    intros c cpos hc IH,
    apply le_antisymm,
    { exact IH lb hlb.1 hlb.2, },
    { exact hlb' c hc cpos, }},
end

-- Demostración de Yakov Pechersky en https://bit.ly/3hAGCZt
example
  (H : set ℤ)
  (x : ℤ)
  (hx : x ∈ H)
  (xpos : 0 < x)
  : ∃! (b : ℤ), 0 < b ∧ b ∈ H ∧ (∀ (c ∈ H), 0 < c → b ≤ c) :=
begin
  set bs : set ℤ := {b : ℤ | b ∈ H ∧ 0 < b} with hbs,
  classical,
  obtain ⟨lb, hlb, hlb'⟩ := @int.exists_least_of_bdd (∈ bs) ⟨0, λ z hz, hz.right.le⟩ ⟨x, hx, xpos⟩,
  simp only [and_imp, set.mem_set_of_eq] at hlb hlb',
  refine ⟨lb, ⟨hlb.right, hlb.left, hlb'⟩, _⟩,
  simp only [and_imp],
  intros c cpos hc IH,
  exact le_antisymm (IH _ hlb.left hlb.right) (hlb' _ hc cpos)
end
