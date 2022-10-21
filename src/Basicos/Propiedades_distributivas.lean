-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones
--    1. Importar la teoría de retículos.
--    2. Declarar α como un tipo sobre retículos
--    3. Declarar a, b y c como variabkes sobre α
-- ----------------------------------------------------------------------

import order.lattice               -- 1
variables {α : Type*} [lattice α]  -- 2
variables a b c : α                -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
-- entonces
--    (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c)
-- ----------------------------------------------------------------------

example
  (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
  : (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c) :=
calc
  (a ⊔ b) ⊓ c = c ⊓ (a ⊔ b)       : by rw inf_comm
          ... = (c ⊓ a) ⊔ (c ⊓ b) : by rw h
          ... = (a ⊓ c) ⊔ (c ⊓ b) : by rw [@inf_comm _ _ c a]
          ... = (a ⊓ c) ⊔ (b ⊓ c) : by rw [@inf_comm _ _ c b]

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si
--    ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)
-- entonces
--    (a ⊓ b) ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
-- ----------------------------------------------------------------------

example
  (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z))
  : (a ⊓ b) ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) :=
calc
  (a ⊓ b) ⊔ c = c ⊔ (a ⊓ b)       : by rw sup_comm
          ... = (c ⊔ a) ⊓ (c ⊔ b) : by rw h
          ... = (a ⊔ c) ⊓ (c ⊔ b) : by rw [@sup_comm _ _ c a]
          ... = (a ⊔ c) ⊓ (b ⊔ c) : by rw [@sup_comm _ _ c b]
