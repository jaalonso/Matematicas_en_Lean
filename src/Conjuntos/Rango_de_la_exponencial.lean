-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que el rango de la función exponencial es el
-- conjunto de los números positivos,
-- ----------------------------------------------------------------------

import analysis.special_functions.exp_log

open set real

example : range exp = { y | y > 0 } :=
begin
  ext y, 
  split,
  { rintros ⟨x, rfl⟩,
    apply exp_pos },
  { intro ypos,
    use log y,
    rw exp_log ypos },
end

-- Prueba
-- ======

/-
⊢ range exp = {y : ℝ | y > 0}
  >> ext y,
y : ℝ
⊢ y ∈ range exp ↔ y ∈ {y : ℝ | y > 0} 
  >> split,
| y : ℝ
| ⊢ y ∈ range exp ↔ y ∈ {y : ℝ | y > 0}
|   >> { rintros ⟨x, rfl⟩
| x : ℝ
| ⊢ x.exp ∈ {y : ℝ | y > 0},
|   >>   apply exp_pos },
y : ℝ
⊢ y ∈ {y : ℝ | y > 0} → y ∈ range exp
  >> { intro ypos,
ypos : y ∈ {y : ℝ | y > 0}
⊢ y ∈ range exp
  >>   use log y,
⊢ y.log.exp = y
  >>   rw exp_log ypos },
⊢ y.log.exp = y
-/

-- Comentario: Se ha usado el lema
-- + exp_log : 0 < x → log (exp x) = x 

variable (x : ℝ)
#check @exp_log x
