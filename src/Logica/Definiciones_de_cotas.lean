-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la librería de los números reales. 
-- ----------------------------------------------------------------------

import data.real.basic

-- ---------------------------------------------------------------------
-- Ejercicio 2. Definir la función
--    fn_ub (ℝ → ℝ) → ℝ → Prop
-- tal que (fn_ub f a) afirma que a es una cota superior de f.
-- ----------------------------------------------------------------------

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

-- ---------------------------------------------------------------------
-- Ejercicio 3. Definir la función
--    fn_lb (ℝ → ℝ) → ℝ → Prop
-- tal que (fn_lb f a) afirma que a es una cota inferior de f.
-- ----------------------------------------------------------------------

def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x
