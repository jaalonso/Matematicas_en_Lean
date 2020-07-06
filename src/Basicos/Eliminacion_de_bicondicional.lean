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
-- Ejercicio 2. Calcular el tipo de los siguientes lemas 
--    add_lt_add_of_le_of_lt
--    exp_lt_exp 
--    le_refl 
-- ----------------------------------------------------------------------

#check @add_lt_add_of_le_of_lt ℝ _ a b c d 
#check @exp_lt_exp a b
#check le_refl 

-- Comentario: Colocando el cursor sobre check se obtiene
--    add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d 
--    exp_lt_exp : a.exp < b.exp ↔ a < b 
--    le_refl : ∀ (a : ?M_1), a ≤ a  

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si
--    a ≤ b 
--    c < d
-- entonces
--    a + exp c + e < b + exp d + e :=
-- ----------------------------------------------------------------------

example 
  (h₀ : a ≤ b) 
  (h₁ : c < d) 
  : a + exp c + e < b + exp d + e :=
begin
  apply add_lt_add_of_lt_of_le,
  { apply add_lt_add_of_le_of_lt h₀,
    apply exp_lt_exp.mpr h₁, },
  apply le_refl
end

-- El desarrollo de la prueba es
-- 
--    a b c d e : ℝ,
--    h₀ : a ≤ b,
--    h₁ : c < d
--    ⊢ a + c.exp + e < b + d.exp + e
-- apply add_lt_add_of_lt_of_le,
-- | { apply add_lt_add_of_le_of_lt h₀,
-- |      ⊢ a + c.exp < b + d.exp
-- |   apply exp_lt_exp.mpr h₁ },
--    ⊢ e ≤ e 
-- apply le_refl
--    no_goals
 
