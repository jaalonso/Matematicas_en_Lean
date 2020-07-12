-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es una función de ℝ en ℝ tal que 
-- para cada a, existe un x tal que f x < a, entonces f no tiene cota
-- inferior.  
-- ----------------------------------------------------------------------

import data.real.basic

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

variable f : ℝ → ℝ

example 
  (h : ∀ a, ∃ x, f x < a) 
  : ¬ fn_has_lb f :=
begin
  intros fnlb,
  cases fnlb with a fnlba,
  cases h a with x hx,
  have : a ≤ f x,
    from fnlba x,
  linarith,
end

-- Prueba
-- ------

-- f : ℝ → ℝ,
-- h : ∀ (a : ℝ), ∃ (x : ℝ), f x < a
-- ⊢ ¬fn_has_lb f
--    >> intros fnlb,
-- fnlb : fn_has_lb f
-- ⊢ false
--    >> cases fnlb with a fnlba,
-- a : ℝ,
-- fnlba : fn_lb f a
-- ⊢ false
--    >> cases h a with x hx,
-- x : ℝ,
-- hx : f x < a
-- ⊢ false
--    >> have : a ≤ f x,
--    >>   from fnlba x,
-- this : a ≤ f x
-- ⊢ false
--    >> linarith,
-- no goals
