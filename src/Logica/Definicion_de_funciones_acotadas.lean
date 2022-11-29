import data.real.basic

-- ---------------------------------------------------------------------
-- Ejercicio 1. Definir la función
--    fn_ub (ℝ → ℝ) → ℝ → Prop
-- tal que (fn_ub f a) afirma que a es una cota superior de f.
-- ----------------------------------------------------------------------

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

-- ---------------------------------------------------------------------
-- Ejercicio 2. Definir la función
--    fn_lb (ℝ → ℝ) → ℝ → Prop
-- tal que (fn_lb f a) afirma que a es una cota inferior de f.
-- ----------------------------------------------------------------------

def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

-- ---------------------------------------------------------------------
-- Ejercicio 3. Definir la función
--    fn_has_ub (ℝ → ℝ) → Prop
-- tal que (fn_has_ub f) afirma que f tiene cota superior.
-- ----------------------------------------------------------------------

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

-- ---------------------------------------------------------------------
-- Ejercicio 4. Definir la función
--    fn_has_lb (ℝ → ℝ) → Prop
-- tal que (fn_has_lb f) afirma que f tiene cota inferior.
-- ----------------------------------------------------------------------

def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a
