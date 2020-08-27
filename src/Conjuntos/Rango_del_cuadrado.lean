import data.real.basic

open set real

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    sqrt '' { x | x ≥ 0 } = {y | y ≥ 0}
-- ----------------------------------------------------------------------

example : sqrt '' { x | x ≥ 0 } = {y | y ≥ 0} :=
begin
  ext,
  split,
  { intro h,
    rcases h with ⟨y,hy,eq⟩,
    simp at *,
    rw ← eq,
    exact sqrt_nonneg y },
  { intro h,
    use x ^ 2,
    simp at *,
    split,
    { exact pow_nonneg h 2 },
    { exact sqrt_sqr h }},
end

-- Prueba
-- ======

/-
⊢ sqrt '' {x : ℝ | x ≥ 0} = {y : ℝ | y ≥ 0}
  >> ext,
x : ℝ
⊢ x ∈ sqrt '' {x : ℝ | x ≥ 0} ↔ x ∈ {y : ℝ | y ≥ 0}
  >> split,
| x : ℝ
| ⊢ x ∈ sqrt '' {x : ℝ | x ≥ 0} → x ∈ {y : ℝ | y ≥ 0}
|   >> { intro h,
| h : x ∈ sqrt '' {x : ℝ | x ≥ 0}
| ⊢ x ∈ {y : ℝ | y ≥ 0}
|   >>   rcases h with ⟨y,hy,eq⟩,
| x y : ℝ,
| hy : y ∈ {x : ℝ | x ≥ 0},
| eq : y.sqrt = x
| ⊢ x ∈ {y : ℝ | y ≥ 0}
|   >>   simp at *,
| hy : 0 ≤ y
| ⊢ 0 ≤ x
|   >>   rw ← eq,
| ⊢ 0 ≤ y.sqrt
|   >>   exact sqrt_nonneg y },
x : ℝ
⊢ x ∈ {y : ℝ | y ≥ 0} → x ∈ sqrt '' {x : ℝ | x ≥ 0}
  >> { intro h,
h : x ∈ {y : ℝ | y ≥ 0}
⊢ x ∈ sqrt '' {x : ℝ | x ≥ 0}
  >>   use x ^ 2,
⊢ x ^ 2 ∈ {x : ℝ | x ≥ 0} ∧ (x ^ 2).sqrt = x
  >>   simp at *,
h : 0 ≤ x
⊢ 0 ≤ x ^ 2 ∧ (x ^ 2).sqrt = x
  >>   split,
| ⊢ 0 ≤ x ^ 2
|   >>   { exact pow_nonneg h 2 },
⊢ (x ^ 2).sqrt = x
  >>   { exact sqrt_sqr h }},
no goals
-/

-- Comentario: Se han usado los lemas
-- + x.sqrt_nonneg : 0 ≤ x.sqrt 
-- + pow_nonneg : 0 ≤ x → ∀ (n : ℕ), 0 ≤ x ^ n 

-- Comprobación: 
variable (x : ℝ)
#check @sqrt_nonneg x
#check @pow_nonneg _ _ x

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    range (λ (x : ℝ), x^2) = {y | y ≥ 0} :=
-- ----------------------------------------------------------------------

example : range (λ (x : ℝ), x^2) = {y | y ≥ 0} :=
begin
  ext,
  split,
  { intro h,
    simp at *,
    rcases h with ⟨y,hy⟩,
    rw ← hy,
    exact pow_two_nonneg y },
  { intro h,
    use sqrt x,
    simp at *,
    exact sqr_sqrt h },
end

-- Prueba
-- ======

/-
⊢ range (λ (x : ℝ), x ^ 2) = {y : ℝ | y ≥ 0}
  >> ext,
x : ℝ
⊢ x ∈ range (λ (x : ℝ), x ^ 2) ↔ x ∈ {y : ℝ | y ≥ 0}
  >> split,
| ⊢ x ∈ range (λ (x : ℝ), x ^ 2) → x ∈ {y : ℝ | y ≥ 0}
|   >> { intro h,
| h : x ∈ range (λ (x : ℝ), x ^ 2)
| ⊢ x ∈ {y : ℝ | y ≥ 0}
|   >>   simp at *,
| h : ∃ (y : ℝ), y ^ 2 = x
| ⊢ 0 ≤ x
|   >>   rcases h with ⟨y,hy⟩,
| x y : ℝ,
| hy : y ^ 2 = x
| ⊢ 0 ≤ x
|   >>   rw ← hy,
| ⊢ 0 ≤ y ^ 2
|   >>   exact pow_two_nonneg y },
x : ℝ
⊢ x ∈ {y : ℝ | y ≥ 0} → x ∈ range (λ (x : ℝ), x ^ 2)
  >> { intro h,
h : x ∈ {y : ℝ | y ≥ 0}
⊢ x ∈ range (λ (x : ℝ), x ^ 2)
  >>   use sqrt x,
⊢ (λ (x : ℝ), x ^ 2) x.sqrt = x
  >>   simp at *,
h : 0 ≤ x
⊢ x.sqrt ^ 2 = x
  >>   exact sqr_sqrt h },
no goals
-/

-- Comentario: Se han usado los lemas
-- + pow_two_nonneg x : 0 ≤ x ^ 2 
-- + sqr_sqrt : 0 ≤ x → (sqrt x) ^ 2 = x 

-- Comprobación:
#check @pow_two_nonneg _ _ x
#check @sqr_sqrt x

