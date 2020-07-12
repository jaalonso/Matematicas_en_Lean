-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la teoría de los números reales.
-- 2. Declarar x e y como variables sobre los reales. 
-- ----------------------------------------------------------------------

import data.real.basic   -- 1
variables {x y : ℝ}      -- 2

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    x^2 + y^2 = 0)
-- entonces
--   x = 0
-- ----------------------------------------------------------------------

lemma aux 
  (h : x^2 + y^2 = 0) 
  : x = 0 :=
begin
  have h' : x^2 = 0,
    { apply le_antisymm,
      show x ^ 2 ≤ 0,
        calc
          x ^ 2 ≤ x^2 + y^2 : by simp [le_add_of_nonneg_right, 
                                       pow_two_nonneg]
            ... = 0         : by exact h,
      apply pow_two_nonneg },
  exact pow_eq_zero h',
end

-- Prueba
-- ======

/-
x y : ℝ,
h : x ^ 2 + y ^ 2 = 0
⊢ x = 0
  >> have h' : x^2 = 0,
| ⊢ x ^ 2 = 0
|   >>   { apply le_antisymm,
| | ⊢ x ^ 2 ≤ 0
|   >>     show x ^ 2 ≤ 0,
|   >>       calc
|   >>         x ^ 2 ≤ x^2 + y^2 : by simp [le_add_of_nonneg_right, 
|   >>                                      pow_two_nonneg]
|   >>           ... = 0         : by exact h,
| ⊢ 0 ≤ x ^ 2
  >>     apply pow_two_nonneg },
h' : x ^ 2 = 0
⊢ x = 0
  >> exact pow_eq_zero h',
no goals
-/

-- Comentario: Los lemas usados son:
-- + le_add_of_nonneg_right : 0 ≤ y → x ≤ x + y
-- + le_antisymm : x ≤ y → y ≤ x → x = y   
-- + pow_eq_zero : ∀ {n : ℕ}, x ^ n = 0 → x = 0
-- + pow_two_nonneg x : 0 ≤ x ^ 2

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--    x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0
-- ----------------------------------------------------------------------

example : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 :=
begin
  split,
    intro h,
    split,
     apply (aux h),
    rw add_comm at h,
    apply (aux h),
  intro h1,
  cases h1 with h2 h3,
  rw [h2, h3],
  ring,
end

-- Prueba
-- ======

/-
x y : ℝ
⊢ x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0
  >> split,
| ⊢ x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0
|   >>   intro h,
| h : x ^ 2 + y ^ 2 = 0
| ⊢ x = 0 ∧ y = 0
|   >>   split,
| | ⊢ x = 0
|   >>    apply (aux h),
| h : y ^ 2 + x ^ 2 = 0
| ⊢ y = 0
|   >>   rw add_comm at h,
|   >>   apply (aux h),
⊢ x = 0 ∧ y = 0 → x ^ 2 + y ^ 2 = 0
  >> intro h1,
h1 : x = 0 ∧ y = 0
⊢ x ^ 2 + y ^ 2 = 0
  >> cases h1 with h2 h3,
h2 : x = 0,
h3 : y = 0
⊢ x ^ 2 + y ^ 2 = 0
  >> rw [h2, h3],
⊢ 0 ^ 2 + 0 ^ 2 = 0
  >> ring,
no goals
-/

-- Comentario: La táctica split, si el objetivo es un bicondicional 
-- (P ↔ Q), aplica la introducción del bicondicional; es decir, lo
-- sustituye por dos nuevos objetivos: P → Q y Q → P.
