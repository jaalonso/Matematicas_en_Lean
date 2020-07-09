-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la teoría de grupos ordenados.
-- 2. Declaral α como un tipo.
-- 3. Declarar R como un monoide ordenado cancelativo.
-- 4. Declarar a, b, c y d como variables sobre R. 
-- ----------------------------------------------------------------------

import algebra.ordered_group                                         -- 1

variables {α : Type*}                                                -- 2
variables {R : Type*} [ordered_cancel_add_comm_monoid R]             -- 3
variables a b c d : R                                                -- 4

-- ---------------------------------------------------------------------
-- Ejercicio 2. Calcular el tipo de
--     @add_le_add R _ a b c d
-- ----------------------------------------------------------------------

#check @add_le_add R _ a b c d

-- Comentario: Al colocar el cursor sobre check se obtiene
--    a ≤ b → c ≤ d → a + c ≤ b + d

-- ---------------------------------------------------------------------
-- Ejercicio 3. Definir la función
--    fn_ub (α → R) → R → Prop
-- tal que (fn_ub f a) afirma que a es una cota superior de f.
-- ----------------------------------------------------------------------

def fn_ub (f : α → R) (a : R) : Prop := ∀ x, f x ≤ a

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que que la suma de una cota superior de f y
-- otra de g es una cota superior de f + g.
-- ----------------------------------------------------------------------

theorem fn_ub_add 
  {f g : α → R} 
  {a b : R}
  (hfa : fn_ub f a) 
  (hgb : fn_ub g b) 
  : fn_ub (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)
