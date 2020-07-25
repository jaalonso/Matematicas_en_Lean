-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar, para todo a ∈ ℝ, si
--    1 < a
-- entonces 
--    a < a * a 
-- ----------------------------------------------------------------------

import data.real.basic

example 
  {a : ℝ} 
  (h : 1 < a) 
  : a < a * a :=
begin
  convert (mul_lt_mul_right _).2 h,
  { rw [one_mul] },
  { exact lt_trans zero_lt_one h },
end

-- Prueba
-- ======

/-
a : ℝ,
h : 1 < a
⊢ a < a * a
  >> convert (mul_lt_mul_right _).2 h,
| 2 goals
| a : ℝ,
| h : 1 < a
| ⊢ a = 1 * a
|   >> { rw [one_mul] },
a : ℝ,
h : 1 < a
⊢ 0 < a
  >> { exact lt_trans zero_lt_one h },
no goals
-/

-- Comentarios:
-- 1. La táctica (convert e) genera nuevos subojetivos cuya conclusiones
--    son las diferencias entre el tipo de ge y la conclusión.
-- 2. Se han usado los siguientes lemas:
--    + mul_lt_mul_right : 0 < c → (a * c < b * c ↔ a < b)
--    + one_mul a : 1 * a = a 
--    + lt_trans : a < b → b < c → a < c 
--    + zero_lt_one : 0 < 1 

-- Comprobación:
variables (a b c : ℝ)
#check @mul_lt_mul_right _ _ a b c
#check @one_mul _ _ a 
#check @lt_trans _ _ a b c
#check @zero_lt_one _ _
