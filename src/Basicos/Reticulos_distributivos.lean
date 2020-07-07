-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
--    1. Importar la teoría de retículos
--    2. Declarar α como un tipo sobre los retículos.
--    3. x, y y z como variables sobre α. 
-- ----------------------------------------------------------------------

import order.lattice                        -- 1
variables {α : Type*} [distrib_lattice α]   -- 2
variables x y z : α                         -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Calcular el tipo de las siguientes expresiones 
--    @inf_sup_left α _ x y z 
--    @inf_sup_right α _ x y z 
--    @sup_inf_left α _ x y z 
--    @sup_inf_right α _ x y z 
-- ----------------------------------------------------------------------

#check @inf_sup_left α _ x y z 
#check @inf_sup_right α _ x y z 
#check @sup_inf_left α _ x y z 
#check @sup_inf_right α _ x y z 

-- Comentario: Al situar el cursor sobre check se obtiene
--    inf_sup_left  : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)
--    inf_sup_right : (x ⊔ y) ⊓ z = (x ⊓ z) ⊔ (y ⊓ z)
--    sup_inf_left  : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)
--    sup_inf_right : (x ⊓ y) ⊔ z = (x ⊔ z) ⊓ (y ⊔ z)
