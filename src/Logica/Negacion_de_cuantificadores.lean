-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Inportar la librería de tácticas.
-- 2. Declarar α como una variable de tipos.
-- 3. Declarar P una variable sobre las propiedades de α. 
-- ----------------------------------------------------------------------

import tactic              -- 1
variables {α : Type*}      -- 2
variables (P : α → Prop)   -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si
--    ¬ ∃ x, P x
-- entonces
--    ∀ x, ¬ P x
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example 
  (h : ¬ ∃ x, P x) 
  : ∀ x, ¬ P x :=
begin
  intros x h1,
  apply h,
  existsi x,
  exact h1,
end

-- Prueba
-- ======

/-
α : Type u_1,
P : α → Prop,
h : ¬∃ (x : α), P x
⊢ ∀ (x : α), ¬P x
  >> intros x h1,
x : α,
h1 : P x
⊢ false
  >> apply h,
⊢ ∃ (x : α), P x
  >> existsi x,
⊢ P x
  >> exact h1,
no goals
-/

-- Comentario: La táctica (existsi e) (ver https://bit.ly/3j21TtU) es la
-- regla de introducción del existencial; es decir, sustituye en el
-- cuerpo del objetivo existencial su variable por e 

example 
  (h : ¬ ∃ x, P x) 
  : ∀ x, ¬ P x :=
not_exists.mp h

-- 3ª demostración
-- ===============

example 
  (h : ¬ ∃ x, P x) 
  : ∀ x, ¬ P x :=
by finish

-- 4ª demostración
-- ===============

example 
  (h : ¬ ∃ x, P x) 
  : ∀ x, ¬ P x :=
by clarify

-- 4ª demostración
-- ===============

example 
  (h : ¬ ∃ x, P x) 
  : ∀ x, ¬ P x :=
by safe

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si
--    ∀ x, ¬ P x
-- entonces
--    ¬ ∃ x, P x
-- ----------------------------------------------------------------------

example 
  (h : ∀ x, ¬ P x) 
  : ¬ ∃ x, P x :=
begin
  intro h1,
  cases h1 with x hx,
  specialize h x,
  apply h hx,
end

-- Prueba
-- ======

/-
α : Type u_1,
P : α → Prop,
h : ∀ (x : α), ¬P x
⊢ ¬∃ (x : α), P x
  >> intro h1,
h1 : ∃ (x : α), P x
⊢ false
  >> cases h1 with x hx,
x : α,
hx : P x
⊢ false
  >> specialize h x,
h : ¬P x
⊢ false
  >> apply h hx,
no goals
-/

-- Comentario: La táctica (specialize h e) (ver https://bit.ly/328xYKy)
-- aplica la rela de eliminación del cuantificador universal a la
-- hipótesis h cambiando su variable  por e.

-- 2ª demostración
-- ===============

example 
  (h : ∀ x, ¬ P x) 
  : ¬ ∃ x, P x :=
not_exists_of_forall_not h

-- 2ª demostración
-- ===============

example 
  (h : ∀ x, ¬ P x) 
  : ¬ ∃ x, P x :=
by finish

-- ---------------------------------------------------------------------
-- Ejercicio 4. Habilitar el uso de las reglas de la lógica clásica. 
-- ----------------------------------------------------------------------

open_locale classical

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que si
--    ¬ ∀ x, P x
-- entonces
--    ∃ x, ¬ P x
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example 
  (h : ¬ ∀ x, P x) 
  : ∃ x, ¬ P x :=
begin
  by_contradiction h',
  apply h,
  intro x,
  by_contradiction h'',
  exact h' ⟨x, h''⟩,
end

-- Prueba
-- ======

/-
α : Type u_1,
P : α → Prop,
h : ¬∀ (x : α), P x
⊢ ∃ (x : α), ¬P x
  >> by_contradiction h',
h' : ¬∃ (x : α), ¬P x
⊢ false
  >> apply h,
⊢ ∀ (x : α), P x
  >> intro x,
x : α
⊢ P x
  >> by_contradiction h'',
h'' : ¬P x
⊢ false
  >> exact h' ⟨x, h''⟩,
no goals
-/

-- Comentarios:
-- 1. La táctica (by_contradiction h) es la regla de reducción al
--    absurdo; es decir, si el objetivo es p añade la hipótesis (h : p) y
--    reduce el objetico a false (ver https://bit.ly/2Ckmadb). 
-- 2. La táctica (exact h1 ⟨x, h2⟩) es la regla de inntroducción del
--    cuantificador existencial; es decir, si el objetivo es de la forma
--    (∃y, P y) demuestra (P x) con h2 y unifica h1 con (∃x, P x). 
--    (ver https://bit.ly/303lLE4).

-- 2ª demostración
-- ===============

example 
  (h : ¬ ∀ x, P x) 
  : ∃ x, ¬ P x :=
not_forall.mp h

-- 2ª demostración
-- ===============

example 
  (h : ¬ ∀ x, P x) 
  : ∃ x, ¬ P x :=
by finish

-- ---------------------------------------------------------------------
-- Ejercicio 6. Demostrar que si
--    ∃ x, ¬ P x
-- entonces
--    ¬ ∀ x, P x
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example 
  (h : ∃ x, ¬ P x) 
  : ¬ ∀ x, P x :=
begin
  intro h1,
  cases h with x hx,
  apply hx,
  exact (h1 x),
end

-- Prueba
-- ======

/-
α : Type u_1,
P : α → Prop,
h : ∃ (x : α), ¬P x
⊢ ¬∀ (x : α), P x
  >> intro h1,
h1 : ∀ (x : α), P x
⊢ false
  >> cases h with x hx,
x : α,
hx : ¬P x
⊢ false
  >> apply hx,
⊢ P x
  >> exact (h1 x)
no goals
-/

-- Comentarios:
-- 1. La táctica (intro h), cuando el objetivo es una negación, es la
--    regla de introducción de la negación; es decir, si el objetivo es
--    ¬P entonces añade la hipótesis (h : P) y cambia el objetivo a
--    false.
-- 2. La táctica (cases h with x hx), cuando la hipótesis es un
--    existencial, es la regla de eliminación del existencial; es decir,
--    si h es (∃ (y : α), P y) añade las hipótesis (x : α) y (hx : P x).

-- 2ª demostración
-- ===============

example 
  (h : ∃ x, ¬ P x) 
  : ¬ ∀ x, P x :=
not_forall.mpr h

-- 3ª demostración
-- ===============

example 
  (h : ∃ x, ¬ P x) 
  : ¬ ∀ x, P x :=
by finish
