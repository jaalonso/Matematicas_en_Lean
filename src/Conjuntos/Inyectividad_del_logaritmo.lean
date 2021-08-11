-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que lo función logarítmica es inyectiva sobre
-- los números positivos.
-- ----------------------------------------------------------------------

import analysis.special_functions.exp_log

open set real

example : inj_on log { x | x > 0 } :=
begin
  intros x xpos y ypos,
  intro h,
  calc
    x   = exp (log x) : by rw exp_log xpos
    ... = exp (log y) : by rw h
    ... = y           : by rw exp_log ypos,
end

-- Prueba
-- ======

/-
⊢ inj_on log {x : ℝ | x > 0}
  >> intros x y xpos ypos,
x y : ℝ,
xpos : x ∈ {x : ℝ | x > 0},
ypos : y ∈ {x : ℝ | x > 0}
⊢ x.log = y.log → x = y
  >> intro h,
h : x.log = y.log
⊢ x = y
  >> calc
  >>   x   = exp (log x) : by rw exp_log xpos
  >>   ... = exp (log y) : by rw h
  >>   ... = y           : by rw exp_log ypos,
-/

-- Comentario: Se ha usado el lema
-- + exp_log : 0 < x → exp (log x) = x

-- Comprobación:
variable (x : ℝ)
-- #check @exp_log x
