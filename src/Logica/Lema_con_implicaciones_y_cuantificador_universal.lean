-- ---------------------------------------------------------------------
-- Ejercicio 1. Importar la librería de los números reales. 
-- ----------------------------------------------------------------------

import data.real.basic

-- ---------------------------------------------------------------------
-- Ejercicio 2. Enunciar el lema ej: "para todos los números reales x,
-- y, ε si  
--    0 < ε  
--    ε ≤ 1  
--    abs x < ε  
--    abs y < ε 
-- entonces 
--    abs (x * y) < ε 
-- ----------------------------------------------------------------------

lemma ej : 
  ∀ x y ε : ℝ,
  0 < ε → 
  ε ≤ 1 → 
  abs x < ε → 
  abs y < ε → 
  abs (x * y) < ε :=
sorry

-- ---------------------------------------------------------------------
-- Ejercicio 3. Crear una sección con las siguientes declaraciones 
--    a b δ : ℝ
--    h₀ : 0 < δ 
--    h₁ : δ ≤ 1
--    ha : abs a < δ 
--    hb : abs b < δ
-- y calcular el tipo de las siguientes expresiones
--    ej a b δ
--    ej a b δ h₀ h₁
--    ej a b δ h₀ h₁ ha hb
-- ----------------------------------------------------------------------

section

variables a b δ : ℝ
variables (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variables (ha : abs a < δ) (hb : abs b < δ)

#check ej a b δ
#check ej a b δ h₀ h₁
#check ej a b δ h₀ h₁ ha hb

-- Comentario: Al colocar el cursor sobre check se obtiene
--    ej a b δ : 0 < δ → δ ≤ 1 → abs a < δ → abs b < δ → abs (a * b) < δ
--    ej a b δ h₀ h₁ : abs a < δ → abs b < δ → abs (a * b) < δ
--    ej a b δ h₀ h₁ ha hb : abs (a * b) < δ

end
