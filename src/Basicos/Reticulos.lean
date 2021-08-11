-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
--    1. Importar la teoría de retículos
--    2. Declarar α como un tipo sobre los retículos.
--    3. x, y y z como variables sobre α.
-- ----------------------------------------------------------------------

import order.lattice                -- 1
variables {α : Type*} [lattice α]   -- 2
variables x y z : α                 -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Calcular el tipo de las siguientes expresiones
--    x ⊓ y
--    @inf_le_left α _ x y
--    @inf_le_right α _ x y
--    @le_inf α _ z x y
--
--    x ⊔ y
--    @le_sup_left α _ x y
--    @le_sup_right α _ x y
--    @sup_le α _ x y z
-- ----------------------------------------------------------------------

-- #check x ⊓ y
-- #check @inf_le_left α _ x y
-- #check @inf_le_right α _ x y
-- #check @le_inf α _ z x y
--
-- #check x ⊔ y
-- #check @le_sup_left α _ x y
-- #check @le_sup_right α _ x y
-- #check @sup_le α _ x y z

-- Comentarios:
-- 1. Para ver cómo se escribe un símbolo, se coloca el cursor sobre el
--    símbolo y se presiona C-c C-k
-- 2. El ínfimo ⊓ se escribe con \glb de "greatest lower bound"
-- 3. El supremo ⊔ se escribe con \lub de "least upper bound"
-- 4. En mathlib se unsa inf o sup para los nombres sobre ínfimo o supremo.
-- 5. Al colocar el cursor sobre check se obtiene
--       x ⊓ y : α
--       inf_le_left : x ⊓ y ≤ x
--       inf_le_right : x ⊓ y ≤ y
--       le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y
--       x ⊔ y : α
--       le_sup_left : x ≤ x ⊔ y
--       le_sup_right: y ≤ x ⊔ y
--       sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z
