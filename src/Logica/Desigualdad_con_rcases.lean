-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1
-- entonces
--    z ≥ 0
-- ----------------------------------------------------------------------

import data.real.basic
import tactic

variables {z : ℝ}      

example 
  (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1) 
  : z ≥ 0 :=
begin
  rcases h with ⟨a, b, h1 | h2⟩,
  { rw h1,
    apply add_nonneg,
    apply pow_two_nonneg,
    apply pow_two_nonneg },
  { rw h2,
    apply add_nonneg,
    apply add_nonneg,
    apply pow_two_nonneg,
    apply pow_two_nonneg,
    exact zero_le_one },
end

-- Prueba
-- ======

/-
z : ℝ,
h : ∃ (x y : ℝ), z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1
⊢ z ≥ 0
  >> rcases h with ⟨a, b, h1 | h2⟩,
| z a b : ℝ,
| h1 : z = a ^ 2 + b ^ 2
| ⊢ z ≥ 0
|   >> { rw h1,
| ⊢ a ^ 2 + b ^ 2 ≥ 0
|   >>   apply add_nonneg,
| | ⊢ 0 ≤ a ^ 2
|   >>   apply pow_two_nonneg,
| ⊢ 0 ≤ b ^ 2
|   >>   apply pow_two_nonneg },
h2 : z = a ^ 2 + b ^ 2 + 1
⊢ z ≥ 0
  >> { rw h2,
⊢ a ^ 2 + b ^ 2 + 1 ≥ 0
  >>   apply add_nonneg,
| ⊢ 0 ≤ a ^ 2 + b ^ 2
|   >>   apply add_nonneg,
| | ⊢ 0 ≤ a ^ 2
| |  >>   apply pow_two_nonneg,
| ⊢ 0 ≤ b ^ 2
|   >>   apply pow_two_nonneg,
⊢ 0 ≤ 1
  >>   exact zero_le_one },
no goals
-/

-- Comentarios:
-- 1. La táctica (rcases h with ⟨a, b, h1 | h2⟩) sobre el objetivo
--    (∃ x y : ℝ, P ‌∨ Q) crea dos casos. Al primero le añade las
--    hipótesis (a b : ℝ) y (k1 : P). Al segundo, (a b : ℝ) y (h2 : Q).
-- 2. Se han usado los siguientes lemas:
--    + add_nonneg : 0 ≤ x → 0 ≤ y → 0 ≤ x + y 
--    + pow_two_nonneg x : 0 ≤ x ^ 2 
--    + zero_le_one : 0 ≤ 1 

-- Comprobación:
variables (x y : ℝ)
#check (@add_nonneg ℝ _ x y) 
#check (@pow_two_nonneg ℝ _ x)
#check zero_le_one
