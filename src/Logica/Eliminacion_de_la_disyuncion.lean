-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que para todo par de números reales x e y, si 
-- x < |y|, entonces x < y ó x < -y.
-- ----------------------------------------------------------------------


import data.real.basic

variables {x y : ℝ}

-- 1ª Demostración
-- ===============

example : x < abs y → x < y ∨ x < -y :=
begin
  cases le_or_gt 0 y with h1 h2,
  { rw abs_of_nonneg h1,
    intro h3, 
    left, 
    exact h3 },
  { rw abs_of_neg h2,
    intro h4, 
    right, 
    exact h4 },
end

-- Prueba
-- ======

/-
x y : ℝ
⊢ x < abs y → x < y ∨ x < -y
  >> cases le_or_gt 0 y with h1 h2,
| h1 : 0 ≤ y
| ⊢ x < abs y → x < y ∨ x < -y
|   >> { rw abs_of_nonneg h1,
| ⊢ x < y → x < y ∨ x < -y
|   >>   intro h3, 
| h3 : x < y
| ⊢ x < y ∨ x < -y
|   >>   left, 
| ⊢ x < y
|   >>   exact h3 },
h2 : 0 > y
⊢ x < abs y → x < y ∨ x < -y
  >> { rw abs_of_neg h2,
⊢ x < -y → x < y ∨ x < -y
  >>   intro h4, 
h4 : x < -y
⊢ x < y ∨ x < -y
  >>   right, 
⊢ x < -y
  >>   exact h4 },
no goals
-/

-- Comentarios:
-- + La táctica (cases h with h1 h2), cuando h es una diyunción, aplica
--   la regla de eliminación de la disyunción; es decir, si h es (P ∨ Q)
--   abre dos casos, en el primero añade la hipótesis (h1 : P) y en el
--   segundo (h2 : Q).  
-- + Se han usado los siguientes lemas
--   + le_or_gt x y : x ≤ y ∨ x > y
--   + abs_of_nonneg : 0 ≤ x → abs x = x
--   + abs_of_neg : x < 0 → abs x = -x

-- Comprobación
#check (@le_or_gt ℝ _ x y)
#check (@abs_of_nonneg ℝ _ x)
#check (@abs_of_neg ℝ _ x)

-- 2ª Demostración
-- ===============

example : x < abs y → x < y ∨ x < -y :=
lt_abs.mp

-- Comentario: Se ha usado el lema
-- + lt_abs : x < abs y ↔ x < y ∨ x < -y

-- Comprobación
#check (@lt_abs ℝ _ x y) 
