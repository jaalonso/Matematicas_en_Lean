-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
--    1. Importar la teoría de órdenes
--    2. Declarar α como un tipo sobre los órdenes parciales
--    3. x, y y z como variables sobre α. 
-- ----------------------------------------------------------------------

import order.basic                        -- 1
variables {α : Type*} [partial_order α]   -- 2
variables x y z : α                       -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Calcular el tipo de las siguientes expresiones 
--    x < y 
--    lt_irrefl x
--    @lt_trans α _ x y z
--    @lt_of_le_of_lt α _ x y z
--    @lt_of_lt_of_le α _ x y z
--    @lt_iff_le_and_ne  α _ x y
-- ----------------------------------------------------------------------

#check x < y 
#check lt_irrefl x
#check @lt_trans α _ x y z
#check @lt_of_le_of_lt α _ x y z
#check @lt_of_lt_of_le α _ x y z
#check @lt_iff_le_and_ne  α _ x y

-- Comentario: Al colocar el cursor sobre check se obtiene
--    x < y : Prop 
--    lt_irrefl x : ¬ x < x
--    lt_trans : x < y → y < z → x < z
--    lt_of_le_of_lt : x ≤ y → y < z → x < z
--    lt_of_lt_of_le : x < y → y ≤ z → x < z
--    lt_iff_le_and_ne : x < y ↔ x ≤ y ∧ x ≠ y
