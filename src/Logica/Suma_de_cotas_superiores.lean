-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la librería de los números reales.
-- 2. Definir cota superior de una función.
-- 3. Definir cota inferior de una función.
-- 4. Declarar f y g como variables de funciones de ℝ en ℝ.
-- 5. Declarar a y b como variables sobre ℝ.
-- ----------------------------------------------------------------------

import data.real.basic                                               -- 1

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a                 -- 2
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x                 -- 3

variables (f g : ℝ → ℝ)                                              -- 4
variables (a b : ℝ)                                                  -- 5

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que la suma de una cota superior de f y una
-- cota superior de g es una cota superior de f + g.
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (hfa : fn_ub f a)
  (hgb : fn_ub g b)
  : fn_ub (λ x, f x + g x) (a + b) :=
begin
  have h1 : ∀ x, f x + g x ≤ a + b,
  { intro x,
    have h1a : f x ≤ a := hfa x,
    have h1b : g x ≤ b := hgb x,
    show f x + g x ≤ a + b,
      by exact add_le_add (hfa x) (hgb x), },
  show fn_ub (λ x, f x + g x) (a + b),
    by exact h1,
end

-- 2ª demostración
-- ===============

example
  (hfa : fn_ub f a)
  (hgb : fn_ub g b)
  : fn_ub (λ x, f x + g x) (a + b) :=
begin
  intro x,
  dsimp,
  change f x + g x ≤ a + b,
  apply add_le_add,
  apply hfa,
  apply hgb
end

-- Su desarrollo es
--
-- f g : ℝ → ℝ,
-- a b : ℝ,
-- hfa : fn_ub f a,
-- hgb : fn_ub g b
-- ⊢ fn_ub (λ (x : ℝ), f x + g x) (a + b)
--    -- intro x,
-- x : ℝ
-- ⊢ (λ (x : ℝ), f x + g x) x ≤ a + b
--    -- change f x + g x ≤ a + b,
-- ⊢ f x + g x ≤ a + b
--    -- apply add_le_add,
-- | ⊢ f x ≤ a
-- |    -- apply hfa,
-- | ⊢ g x ≤ b
-- |    -- apply hgb
-- no goals

-- Notas.
-- + Nota 1. Con "intro x" se despliega la definición de fn_ub y se introduce
--   la variable x en el contexto.
-- + Nota 2. Con "dsimp" se simplifica la definición del lambda. El mismo
--   efecto se consigue con "change f x + g x ≤ a + b"

-- 3ª demostración
-- ===============

example
  (hfa : fn_ub f a)
  (hgb : fn_ub g b)
  : fn_ub (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)
