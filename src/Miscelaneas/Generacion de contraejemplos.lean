import tactic.slim_check

-- example
--   (a : ℕ)
--   : ∀ {l₁ l₂ : list ℕ}, a ∈ l₁.diff l₂ → a ∈ l₁ ∧ a ∉ l₂ :=
-- by slim_check

/-
 Al descomentarlo da

 ===================
 Found problems!

 a := 0
 l₁ := [4, 4, 11, 178, 7, 5, 0, 0]
 l₂ := [511, 0, 2, 8, 3]
 (0 shrinks)
 -------------------
-/


-- lemma dvd_mul_a_b_then_a_or_b {a b x : ℕ} (h: (x ∣ (a*b))) : x ∣ a ∨ x ∣ b :=
-- by slim_check

/-
 Al descomentarlo da

 ===================
 Found problems!

 a := 10
 b := 6
 x := 4
 (0 shrinks)
 -------------------

 state:
 a b x : ℕ,
 h : x ∣ a * b
 ⊢ x ∣ a ∨ x ∣ b
-/
