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
-- Ejercicio 2. Calcular los tipos de las siguientes expresiones
--    x ≤ y
--    le_refl x
--    @le_trans α _ x y z
-- ----------------------------------------------------------------------

-- #check x ≤ y
-- #check le_refl x
-- #check @le_trans α _ x y z

-- Conentario: Al colocar el cursor sobre check se obtiene
--    x ≤ y : Prop
--    le_refl x : x ≤ x)
--    le_trans : x ≤ y → y ≤ z → x ≤ z)

-- Nota: Las letras griegas se escriben con \a, \b, ...
