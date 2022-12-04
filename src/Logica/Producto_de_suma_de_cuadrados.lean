-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la librería de tácticas.
-- 2. Declarar α como un tipo sobre los anillos conmutativos.
-- 3. Declarar x e y como variables sobre α.
-- ----------------------------------------------------------------------

import tactic
variables {α : Type*} [comm_ring α]
variables {x y : α}

-- ---------------------------------------------------------------------
-- Ejercicio 2. Definir la función
--    sum_of_squares : α → Prop
-- tal que (sum_of_squares x) afima que x se puede escribir como la suma
-- de dos cuadrados.
-- ----------------------------------------------------------------------

def sum_of_squares (x : α) := ∃ a b, x = a^2 + b^2

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si x e y se pueden escribir como la suma
-- de dos cuadrados, entonces también se puede escribir x * y.
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (sosx : sum_of_squares x)
  (sosy : sum_of_squares y)
  : sum_of_squares (x * y) :=
begin
  rcases sosx with ⟨a, b, xeq : x = a^2 + b^2⟩,
  rcases sosy with ⟨c, d, yeq : y = c^2 + d^2⟩,
  have h1: x * y = (a*c - b*d)^2 + (a*d + b*c)^2,
    calc x * y
         = (a^2 + b^2) * (c^2 + d^2)     : by rw [xeq, yeq]
     ... = (a*c - b*d)^2 + (a*d + b*c)^2 : by ring,
  have h2 : ∃ f, x * y = (a*c - b*d)^2 + f^2,
    by exact Exists.intro (a*d + b*c) h1,
  have h3 : ∃ e f, x * y = e^2 + f^2,
    by exact Exists.intro (a*c - b*d) h2,
  show sum_of_squares (x * y),
    by exact h3,
end

-- 2ª demostración
-- ===============

example
  (sosx : sum_of_squares x)
  (sosy : sum_of_squares y)
  : sum_of_squares (x * y) :=
begin
  rcases sosx with ⟨a, b, xeq : x = a^2 + b^2⟩,
  rcases sosy with ⟨c, d, yeq : y = c^2 + d^2⟩,
  have h1: x * y = (a*c - b*d)^2 + (a*d + b*c)^2,
    calc x * y
         = (a^2 + b^2) * (c^2 + d^2)     : by rw [xeq, yeq]
     ... = (a*c - b*d)^2 + (a*d + b*c)^2 : by ring,
  have h2 : ∃ e f, x * y = e^2 + f^2,
    by tauto,
  show sum_of_squares (x * y),
    by exact h2,
end

-- 3ª demostración
-- ===============

example
  (sosx : sum_of_squares x)
  (sosy : sum_of_squares y)
  : sum_of_squares (x * y) :=
begin
  rcases sosx with ⟨a, b, xeq⟩,
  rcases sosy with ⟨c, d, yeq⟩,
  rw [xeq, yeq],
  use [a*c - b*d, a*d + b*c],
  ring,
end

-- Su desarrollo es
--
-- α : Type u_1,
-- _inst_1 : comm_ring α,
-- x y : α,
-- sosx : sum_of_squares x,
-- sosy : sum_of_squares y
-- ⊢ sum_of_squares (x * y)
--    >> rcases sosx with ⟨a, b, xeq⟩,
-- α : Type u_1,
-- _inst_1 : comm_ring α,
-- x y : α,
-- sosy : sum_of_squares y,
-- a b : α,
-- xeq : x = a ^ 2 + b ^ 2
-- ⊢ sum_of_squares (x * y)
--    >> rcases sosy with ⟨c, d, yeq⟩,
-- α : Type u_1,
-- _inst_1 : comm_ring α,
-- x y a b : α,
-- xeq : x = a ^ 2 + b ^ 2,
-- c d : α,
-- yeq : y = c ^ 2 + d ^ 2
-- ⊢ sum_of_squares (x * y)
--    >> rw [xeq, yeq],
-- ⊢ sum_of_squares ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2))
--    >> use [a*c - b*d, a*d + b*c],
-- ⊢ (a^2 + b^2) * (c^2 + d^2) = (a * c - b * d)^2 + (a * d + b * c)^2
--    >> ring
-- no goals

-- 3ª demostración
-- ===============

example
  (sosx : sum_of_squares x)
  (sosy : sum_of_squares y)
  : sum_of_squares (x * y) :=
begin
  rcases sosx with ⟨a, b, rfl⟩,
  rcases sosy with ⟨c, d, rfl⟩,
  use [a*c - b*d, a*d + b*c],
  ring
end

-- Su desarrollo es
--
-- α : Type u_1,
-- _inst_1 : comm_ring α,
-- x y : α,
-- sosx : sum_of_squares x,
-- sosy : sum_of_squares y
-- ⊢ sum_of_squares (x * y)
--    >> rcases sosx with ⟨a, b, rfl⟩,
-- α : Type u_1,
-- _inst_1 : comm_ring α,
-- x y : α,
-- sosy : sum_of_squares y,
-- a b : α,
-- xeq : x = a ^ 2 + b ^ 2
-- ⊢ sum_of_squares (x * y)
--    >> rcases sosy with ⟨c, d, rfl⟩,
-- α : Type u_1,
-- _inst_1 : comm_ring α,
-- x y a b : α,
-- xeq : x = a ^ 2 + b ^ 2,
-- c d : α,
-- yeq : y = c ^ 2 + d ^ 2
-- ⊢ sum_of_squares (x * y)
--    >> use [a*c - b*d, a*d + b*c],
-- ⊢ (a^2 + b^2) * (c^2 + d^2) = (a * c - b * d)^2 + (a * d + b * c)^2
--    >> ring
-- no goals
