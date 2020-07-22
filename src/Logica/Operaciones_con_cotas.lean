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
-- Ejercicio 2. Demostrar que la suma de una cota inferior de f y una
-- cota inferior de g es una cota inferior de f + g.
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (hfa : fn_lb f a) 
  (hgb : fn_lb g b) 
  : fn_lb (λ x, f x + g x) (a + b) :=
begin
  intro x,
  change a + b ≤ f x + g x,
  apply add_le_add,
  apply hfa,
  apply hgb
end

-- Su desarrollo es
--
-- f g : ℝ → ℝ,
-- a b : ℝ,
-- hfa : fn_lb f a,
-- hgb : fn_lb g b
-- ⊢ fn_lb (λ (x : ℝ), f x + g x) (a + b)
--    -- intro x,
-- x : ℝ
-- ⊢ a + b ≤ (λ (x : ℝ), f x + g x) x
--    -- change a + b ≤ f x + g x,
-- ⊢ a + b ≤ f x + g x
--    -- apply add_le_add,
-- | ⊢ a ≤ f x
-- |    -- apply hfa,
-- | ⊢ b ≤ g x
-- |    -- apply hgb
-- no goals

-- 2ª demostración
-- ===============

example
  (hfa : fn_lb f a) 
  (hgb : fn_lb g b) 
  : fn_lb (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que el producto de dos funciones no negativas
-- es no negativa.
-- ----------------------------------------------------------------------

example
  (nnf : fn_lb f 0) 
  (nng : fn_lb g 0) 
  : fn_lb (λ x, f x * g x) 0 :=
begin
  intro x,
  change 0 ≤ f x * g x,
  apply mul_nonneg,
  apply nnf,
  apply nng
end

-- Su desarrollo es
--
-- f g : ℝ → ℝ,
-- nnf : fn_lb f 0,
-- nng : fn_lb g 0
-- ⊢ fn_lb (λ (x : ℝ), f x * g x) 0 
--    -- intro x,
-- x : ℝ
-- ⊢ 0 ≤ (λ (x : ℝ), f x * g x) x
--    -- change 0 ≤ f x * g x,
-- ⊢ 0 ≤ f x * g x
--    -- apply mul_nonneg,
-- | ⊢ 0 ≤ f x
-- |    -- apply nnf,
-- | ⊢ 0 ≤ g x
-- |    -- apply nng
-- no goals

-- 2ª demostración
-- ===============

example
  (nnf : fn_lb f 0) 
  (nng : fn_lb g 0) 
  : fn_lb (λ x, f x * g x) 0 :=
λ x, mul_nonneg (nnf x) (nng x)

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que si a es una cota superior de f, b es una
-- cota superior de g, a es no negativa y g es no negativa, entonces 
-- a * b es una cota superior de f * g.
-- ----------------------------------------------------------------------

example
  (hfa : fn_ub f a) 
  (hfb : fn_ub g b)
  (nng : fn_lb g 0) 
  (nna : 0 ≤ a) 
  : fn_ub (λ x, f x * g x) (a * b) :=
begin
  intro x,
  change f x * g x ≤ a * b,
  apply mul_le_mul,
  apply hfa,
  apply hfb,
  apply nng,
  apply nna
end

-- Su desarrollo es
-- 
-- f g : ℝ → ℝ,
-- a b : ℝ,
-- hfa : fn_ub f a,
-- hfb : fn_ub g b,
-- nng : fn_lb g 0,
-- nna : 0 ≤ a
-- ⊢ fn_ub (λ (x : ℝ), f x * g x) (a * b)
--    -- intro x,
-- x : ℝ
-- ⊢ (λ (x : ℝ), f x * g x) x ≤ a * b
--    -- change f x * g x ≤ a * b,
-- ⊢ f x * g x ≤ a * b
--    -- apply mul_le_mul,
-- | ⊢ f x ≤ a
-- |    -- apply hfa,
-- | g x ≤ b
-- |    -- apply hfb,
-- | 0 ≤ g x
-- |    -- apply nng,
-- | 0 ≤ a
-- |    -- apply nna
-- no goals

-- 2ª demostración
-- ===============

example 
  (hfa : fn_ub f a)     
  (hfb : fn_ub g b)
  (nng : fn_lb g 0) 
  (nna : 0 ≤ a) 
  : fn_ub (λ x, f x * g x) (a * b) :=
begin
  dunfold fn_ub fn_lb at *,
  intro x,
  have h1:= hfa x,
  have h2:= hfb x,
  have h3:= nng x,
  exact mul_le_mul h1 h2 h3 nna,
end

-- Prueba
-- ======

/-
f g : ℝ → ℝ,
a b : ℝ,
hfa : fn_ub f a,
hfb : fn_ub g b,
nng : fn_lb g 0,
nna : 0 ≤ a
⊢ fn_ub (λ (x : ℝ), f x * g x) (a * b)
  >> dunfold fn_ub fn_lb at *,
hfa : ∀ (x : ℝ), f x ≤ a,
hfb : ∀ (x : ℝ), g x ≤ b,
nng : ∀ (x : ℝ), 0 ≤ g x,
nna : 0 ≤ a
⊢ ∀ (x : ℝ), f x * g x ≤ a * b
  >> intro x,
x : ℝ
⊢ f x * g x ≤ a * b
  >> have h1:= hfa x,
h1 : f x ≤ a
⊢ f x * g x ≤ a * b
  >> have h2:= hfb x,
h2 : g x ≤ b
⊢ f x * g x ≤ a * b
  >> have h3:= nng x,
h3 : 0 ≤ g x
⊢ f x * g x ≤ a * b
  >> exact mul_le_mul h1 h2 h3 nna,
no goals
-/

-- 3ª demostración
-- ===============

example 
  (hfa : fn_ub f a) 
  (hfb : fn_ub g b)
  (nng : fn_lb g 0) 
  (nna : 0 ≤ a) 
  : fn_ub (λ x, f x * g x) (a * b) :=
begin
  dunfold fn_ub fn_lb at *,
  intro x,
  specialize hfa x,
  specialize hfb x,
  specialize nng x,
  exact mul_le_mul hfa hfb nng nna,
end

-- Prueba
-- ======

/-
f g : ℝ → ℝ,
a b : ℝ,
hfa : fn_ub f a,
hfb : fn_ub g b,
nng : fn_lb g 0,
nna : 0 ≤ a
⊢ fn_ub (λ (x : ℝ), f x * g x) (a * b)
  >> dunfold fn_ub fn_lb at *,
hfa : ∀ (x : ℝ), f x ≤ a,
hfb : ∀ (x : ℝ), g x ≤ b,
nng : ∀ (x : ℝ), 0 ≤ g x,
nna : 0 ≤ a
⊢ ∀ (x : ℝ), f x * g x ≤ a * b
  >> intro x,
x : ℝ
⊢ f x * g x ≤ a * b
  >> specialize hfa x,
hfa : f x ≤ a
⊢ f x * g x ≤ a * b
  >> specialize hfb x,
hfb : g x ≤ b
⊢ f x * g x ≤ a * b
  >> specialize nng x,
nng : 0 ≤ g x
⊢ f x * g x ≤ a * b
  >> exact mul_le_mul hfa hfb nng nna,
no goals
-/

-- 4ª demostración
-- ===============

example
  (hfa : fn_ub f a) 
  (hfb : fn_ub g b)
  (nng : fn_lb g 0) 
  (nna : 0 ≤ a) 
  : fn_ub (λ x, f x * g x) (a * b) :=
λ x, mul_le_mul (hfa x) (hfb x) (nng x) nna
