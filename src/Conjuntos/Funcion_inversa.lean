-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones:
-- 1. Importar la teoría data.set.function
-- 2. Declarar u y v como universos.
-- 3. Declarar α como variable sobre tipo de u habitados.
-- 4. Declarar β como variable sobre tipo de v.
-- 5. Declarar la teoría como no computable.
-- 6. Usar la lógica clásica.
-- ----------------------------------------------------------------------

import data.set.function               -- 1
universes u v                          -- 2
variables {α : Type u} [inhabited α]   -- 3
variables {β : Type v}                 -- 4
noncomputable theory                   -- 5
open_locale classical                  -- 6

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la inversa de una función 
-- ----------------------------------------------------------------------

def inverse (f : α → β) : β → α :=
λ y : β, if h : ∃ x, f x = y 
         then classical.some h 
         else default α

-- ---------------------------------------------------------------------
-- Ejercicio. Sea d una función de α en β e y un elemento de
-- β. Demostrar que si 
--    ∃ x, f x = y
-- entonces
--    f (inverse f y) = y :=
-- ----------------------------------------------------------------------

theorem inverse_spec 
  {f : α → β} 
  (y : β) 
  (h : ∃ x, f x = y) :
  f (inverse f y) = y :=
begin
  rw inverse, dsimp, rw dif_pos h,
  exact classical.some_spec h
end

-- Prueba
-- ======

/-
α : Type u,
_inst_1 : inhabited α,
β : Type v,
f : α → β,
y : β,
h : ∃ (x : α), f x = y
⊢ f (inverse f y) = y
  >> rw inverse, dsimp, rw dif_pos h,
⊢ f (classical.some h) = y
  >> exact classical.some_spec h,
no goals
-/

-- Comentarios: 
-- 1. La identidad (dif_pos h), cuando (h : e), reescribe la expresión
--    (if h : e then x else y) a x. 
-- 2. La identidad (dif_neg h), cuando (h : ¬ e), reescribe la expresión
--    (if h : e then x else y) a y. 
