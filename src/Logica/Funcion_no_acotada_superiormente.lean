-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es una función de ℝ en ℝ tal que 
-- para cada a, existe un x tal que f x > a, entonces f no tiene cota
-- superior.  
-- ----------------------------------------------------------------------

import data.real.basic

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

variable f : ℝ → ℝ

lemma no_has_ub 
  (h : ∀ a, ∃ x, f x > a) 
  : ¬ fn_has_ub f :=
begin
  intros fnub,
  cases fnub with a fnuba,
  cases h a with x hx,
  have : f x ≤ a,
    from fnuba x,
  linarith,
end

-- Prueba
-- ------

-- f : ℝ → ℝ,
-- h : ∀ (a : ℝ), ∃ (x : ℝ), f x > a
-- ⊢ ¬fn_has_ub f
--    >> intros fnub,
-- fnub : fn_has_ub f
-- ⊢ false
--    >> cases fnub with a fnuba,
-- a : ℝ,
-- fnuba : fn_ub f a
-- ⊢ false
--    >> cases h a with x hx,
-- x : ℝ,
-- hx : f x > a
-- ⊢ false
--    >> have : f x ≤ a,
--    >>   from fnuba x,
-- this : f x ≤ a
-- ⊢ false
--    >> linarith,
-- no goals

