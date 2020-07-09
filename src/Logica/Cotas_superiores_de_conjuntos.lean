-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Declarar α como un tipo sobre órdenes parciales.
-- 2. Declarar s como una variable sobre conjuntos de elementos de tipo α
-- 3. Declarar a y b como variables sobre α. 
-- ----------------------------------------------------------------------

variables {α : Type*} [partial_order α]                               -- 1
variables (s : set α)                                                 -- 2
variables (a b : α)                                                   -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Definir la función
--    set_ub : set α → α → Prop
-- tal que (set_ub s a) afirma que a es una cota superior de s. 
-- ----------------------------------------------------------------------


def set_ub (s : set α) (a : α) := ∀ x, x ∈ s → x ≤ a

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si a es una cota superior de s y a ≤ b,
-- entonces b es una cota superior de s.
-- ----------------------------------------------------------------------

example 
  (h : set_ub s a) 
  (h' : a ≤ b) 
  : set_ub s b :=
begin
  intros x xs,
  calc 
    x   ≤ a : (h x xs)
    ... ≤ b : h'
end

