-- ---------------------------------------------------------------------
-- Ejercicio. Sea x un número real. Demostrar que si 
--    x ≠ 0
-- entonces
--    x < 0 ∨ x > 0
 -- ----------------------------------------------------------------------

import data.real.basic

example 
  {x : ℝ} 
  (h : x ≠ 0) 
  : x < 0 ∨ x > 0 :=
begin
  rcases lt_trichotomy x 0 with xlt | xeq | xgt,
  { left, 
    exact xlt },
  { contradiction },
  { right, 
    exact xgt },
end

-- Prueba
-- ======

/-
x : ℝ,
h : x ≠ 0
⊢ x < 0 ∨ x > 0
  >> rcases lt_trichotomy x 0 with xlt | xeq | xgt,
| | xlt : x < 0
| | ⊢ x < 0 ∨ x > 0
| |   >> { left,
| | ⊢ x < 0 
| |   >>  exact xlt },
| h : x ≠ 0,
| xeq : x = 0
| ⊢ x < 0 ∨ x > 0
  >> { contradiction },
h : x ≠ 0,
xgt : 0 < x
⊢ x < 0 ∨ x > 0
  >> { right, 
⊢ x > 0
  >>  exact xgt },
no goals
-/

-- Comentarios:
-- 1. La táctica (rcases h with h1 | h2 | h3) si el objetivo es (P ∨ Q ∨ R)
--    crea tres casos añadiéndole al primero la hipótesis (h1 : P), al
--    segundo (h2 : Q) y al tercero (h3 : R). 
