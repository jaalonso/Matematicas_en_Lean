-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones:
-- 1. Importar la librería data.set.lattice
-- 2. Abrir el espacio de nombres set.
-- 3. Declarar α una variable de tipos.
-- 4. Declarar s una vabiable sobre conjuntos de conjuntos de elementos
--    de α.
-- ----------------------------------------------------------------------

import data.set.lattice      -- 1
open set                     -- 2 
variable {α : Type*}         -- 3
variable (s : set (set α))   -- 4

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    ⋃₀ s = ⋃ t ∈ s, t
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : ⋃₀ s = ⋃ t ∈ s, t :=
begin
  ext x,
  rw mem_bUnion_iff,
  refl,
end

-- Prueba
-- ======

/-
α : Type u_1,
s : set (set α)
⊢ ⋃₀ s = ⋃ (t : set α) (H : t ∈ s), t
  >> ext x,
x : α
⊢ x ∈ ⋃₀ s ↔ x ∈ ⋃ (t : set α) (H : t ∈ s), t
  >> rw mem_bUnion_iff,
⊢ x ∈ ⋃₀ s ↔ ∃ (x_1 : set α) (H : x_1 ∈ s), x ∈ x_1
  >> refl,
no goals
-/

-- Comentario: Se ha usado el lema
-- + mem_bUnion_iff: y ∈ (⋃ x ∈ s, t x) ↔ ∃ x ∈ s, y ∈ t x

-- 2ª demostración
-- ===============

example : ⋃₀ s = ⋃ t ∈ s, t :=
sUnion_eq_bUnion

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    ⋂₀ s = ⋂ t ∈ s, t
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : ⋂₀ s = ⋂ t ∈ s, t :=
begin
  ext x,
  rw mem_bInter_iff,
  refl,
end

-- Prueba
-- ======

/-
α : Type u_1,
s : set (set α)
⊢ ⋂₀ s = ⋂ (t : set α) (H : t ∈ s), t
  >> ext x,
x : α
⊢ x ∈ ⋂₀ s ↔ x ∈ ⋂ (t : set α) (H : t ∈ s), t
  >> rw mem_bInter_iff,
⊢ x ∈ ⋂₀ s ↔ ∀ (x_1 : set α), x_1 ∈ s → x ∈ x_1
  >> refl,
no goals
-/

-- Comentario: Se ha usado el lema
-- + mem_bInter_iff : y ∈ (⋂ x ∈ s, t x) ↔ ∀ x ∈ s, y ∈ t x 

-- 2ª demostración
-- ===============

example : ⋂₀ s = ⋂ t ∈ s, t :=
sInter_eq_bInter


