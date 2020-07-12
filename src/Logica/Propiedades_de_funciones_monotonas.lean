-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones
-- 1. Importar la librería de los reales.
-- 2. Declarar f como variable de las funciones de ℝ en ℝ.
-- 3. Declarar a y b como variables sobre los reales. 
-- ----------------------------------------------------------------------

import data.real.basic   -- 1
variables (f : ℝ → ℝ)    -- 2
variables (a b : ℝ)      -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si f es monótona y f(a) < f(b), entonces  
-- a < b
-- ----------------------------------------------------------------------

example 
  (h : monotone f) 
  (h' : f a < f b) 
  : a < b :=
begin
  apply lt_of_not_ge,
  intro hab,
  have : f a ≥ f b,
    from h hab,
  linarith,
end

-- Prueba
-- ======

-- f : ℝ → ℝ,
-- a b : ℝ,
-- h : monotone f,
-- h' : f a < f b
-- ⊢ a < b
--    >> apply lt_of_not_ge,
-- ⊢ ¬a ≥ b
--    >> intro hab,
-- hab : a ≥ b
-- ⊢ false
--    >> have : f a ≥ f b,
--    >>   from h hab,
-- this : f a ≥ f b
-- ⊢ false
--    >> linarith,
-- no goals

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si
--    a ≤ b 
--    f b < f a
-- entonces f no es monótona. 
-- ----------------------------------------------------------------------

example 
  (h : a ≤ b) 
  (h' : f b < f a) 
  : ¬ monotone f :=
begin
  intro h1,
  have : f a ≤ f b,
    from h1 h,
  linarith,
end

-- Prueba
-- ======

-- f : ℝ → ℝ,
-- a b : ℝ,
-- h : a ≤ b,
-- h' : f b < f a
-- ⊢ ¬monotone f
--    >> intro h1,
-- h1 : monotone f
-- ⊢ false
--    >> have : f a ≤ f b,
--    >>   from h1 h,
-- this : f a ≤ f b
-- ⊢ false
--    >> linarith,
-- no goals
