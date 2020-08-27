-- El enunciado está en https://bit.ly/2YFUdVt y y varias soluciones en 
-- https://bit.ly/3jk4gHC
-- 
-- La conversación en Zulip es https://bit.ly/34FUiwa

import data.real.basic
import analysis.normed_space.basic

example 
  (f g : ℝ → ℝ)
  (hf1 : ∀ x, ∀ y, (f (x+y) + f(x-y)) = 2 * f(x) * g(y))
  (hf2 : ∀ y, ∥f(y)∥ ≤ 1)
  (hf3 : ∃ x, f(x) ≠ 0)
  (y : ℝ) 
  : ∥g(y)∥ ≤ 1 :=
begin
  classical,
  set S := set.range (λ x, ∥f x∥),
  set k : ℝ := Sup S,
  have h1 : ∃ x, ∀ y ∈ S, y ≤ x,
  { use 1,
    intros fz zs,
    obtain ⟨z, rfl⟩ := zs,
    apply hf2 },
  have h2 : ∀ x, ∥f x∥ ≤ k,
  {
    intro x,
    apply real.le_Sup,
    { assumption },
    { apply set.mem_range_self, },
  },
  have h3 : 0 < k,
  { obtain ⟨x, hx⟩ := hf3,
    calc 0
        < ∥f x∥ : norm_pos_iff.mpr hx
    ... ≤ k : h2 x,
  },
  have h4 : ∃ x : ℝ, x ∈ S,
  { use ∥f 0∥, exact set.mem_range_self 0, },
  have h5 : ∀ x, _,
  { intro x,
    calc 2 * (∥f x∥ * ∥g y∥)
        = ∥2 * f x * g y∥           : by simp [real.norm_eq_abs, abs_mul, 
                                               mul_assoc]
    ... = ∥f (x + y) + f (x - y)∥   : by rw hf1
    ... ≤ ∥f (x + y)∥ + ∥f (x - y)∥ : norm_add_le _ _
    ... ≤ k + k                     : add_le_add (h2 _) (h2 _)
    ... = 2 *k                      : (two_mul _).symm,
  },
  have h5': ∀ (x : ℝ), ∥f x∥ * ∥g y∥ ≤ k,
  { intro x,
    apply (mul_le_mul_left zero_lt_two).mp (h5 x),
  },

  by_contra,
  push_neg at a,

  set k' := k / ∥g y∥,
  have h6 : ∀ x, ∥f x∥ ≤ k',
  { intros x,
    rw le_div_iff,
    { apply h5', },
    exact trans zero_lt_one a, },
  have h7 : k' < k,
  { rw div_lt_iff,
    apply lt_mul_of_one_lt_right ‹0 < k› a,
    exact trans zero_lt_one a },
  have h8 : k ≤ k',
  { apply real.Sup_le_ub _ h4,
    rintros y' ⟨yy, rfl⟩,
    apply h6,
  },
  apply lt_irrefl k',
  calc k'
      < k : ‹_›
  ... ≤ k' : ‹_›
end
