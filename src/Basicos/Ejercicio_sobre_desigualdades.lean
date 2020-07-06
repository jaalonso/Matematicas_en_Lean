-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones
--    1. Importar la teoría de exponeciales y logaritmos.
--    2. Abrir la teoría de los reales
--    3. Declarar a, b, c, d y e como variables sobre los reales.
-- ----------------------------------------------------------------------

import analysis.special_functions.exp_log   -- 1
open real                                   -- 2
variables a b c d e : ℝ                     -- 3 

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    d ≤ e
-- entonces
--    c + exp (a + d) ≤ c + exp (a + e)
-- ----------------------------------------------------------------------

example 
  (h₀ : d ≤ e) 
  : c + exp (a + d) ≤ c + exp (a + e) :=
begin
  apply add_le_add,
   apply le_refl,
  apply exp_le_exp.mpr,
  apply add_le_add,
   apply le_refl,
  exact h₀,
end

-- El desarrollo de la prueba es
--
--    a c d e : ℝ,
--    h₀ : d ≤ e
--    ⊢ c + (a + d).exp ≤ c + (a + e).exp
-- apply add_le_add,
-- |   ⊢ c ≤ c
-- | apply le_refl,
--    ⊢ (a + d).exp ≤ (a + e).exp
-- apply exp_le_exp.mpr,
--    ⊢ a + d ≤ a + e
-- apply add_le_add,
-- |    ⊢ a ≤ a
-- | apply le_refl,
--    ⊢ d ≤ e
-- exact h₀,
--    no goals

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--    0 < 1
-- ----------------------------------------------------------------------

example : (0 : ℝ) < 1 :=
by norm_num

-- Nota: La táctica norm_num normaliza expresiones numéricas. Ver 
-- https://bit.ly/3hoJMgQ

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que si
--    a ≤ b
-- entonces 
--    log (1 + exp a) ≤ log (1 + exp b) :=
-- ----------------------------------------------------------------------

example 
  (h : a ≤ b) 
  : log (1 + exp a) ≤ log (1 + exp b) :=
begin
  have h₀ : 0 < 1 + exp a,
  { apply add_pos,
    norm_num,
    apply exp_pos, },
  have h₁ : 0 < 1 + exp b,
  { apply add_pos,
    norm_num,
    apply exp_pos },
  apply (log_le_log h₀ h₁).mpr,
  apply add_le_add,
   apply le_refl,
  apply exp_le_exp.mpr h,
end

-- El desarrollo de la prueba es
--
--    a b : ℝ,
--    h : a ≤ b
--    ⊢ (1 + a.exp).log ≤ (1 + b.exp).log
-- have h₀ : 0 < 1 + exp a,
-- |    ⊢ 0 < 1 + a.exp
-- | apply add_pos,
-- |    ⊢ 0 < 1
-- | norm_num,
-- |    ⊢ 0 < a.exp
-- | apply exp_pos },
--    a b : ℝ,
--    h : a ≤ b,
--    h₀ : 0 < 1 + a.exp
--    ⊢ (1 + a.exp).log ≤ (1 + b.exp).log
-- have h₁ : 0 < 1 + exp b,
--    ⊢ 0 < 1 + b.exp
-- | apply add_pos,
-- |    ⊢ 0 < 1
-- | norm_num,
-- |    0 < b.exp
-- | apply exp_pos },
--    a b : ℝ,
--    h : a ≤ b,
--    h₀ : 0 < 1 + a.exp,
--    h₁ : 0 < 1 + b.exp
--    ⊢ (1 + a.exp).log ≤ (1 + b.exp).log
-- apply (log_le_log h₀ h₁).mpr,
--    ⊢ 1 + a.exp ≤ 1 + b.exp
-- apply add_le_add,
-- |    ⊢ 1 ≤ 1
-- | apply le_refl,
--    ⊢ a.exp ≤ b.exp
-- apply exp_le_exp.mpr h,
--    no goals

-- Comentario. Los lemas empleados son
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (le_refl : ∀ (a : real), a ≤ a)
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check (log_le_log : 0 < a → 0 < b → (log a ≤ log b ↔ a ≤ b))
