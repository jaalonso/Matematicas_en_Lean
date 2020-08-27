import .Funcion_inversa

universes u v                          
variables {α : Type u} [inhabited α]   
variables {β : Type v}                 
variable  f : α → β
variable  g : β → α
variable  x : α

open set function

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que g es la inversa por la izquierda de f syss
--    ∀ x, g (f x) = x
-- ----------------------------------------------------------------------

example : left_inverse g f ↔ ∀ x, g (f x) = x :=
by rw left_inverse

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que las siguientes condiciones son equivalentes:
-- 1. f es inyectiva
-- 2. left_inverse (inverse f) f
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : injective f ↔ left_inverse (inverse f) f  :=
begin
  split,
  { intros h y,
    apply h,
    apply inverse_spec,
    use y },
  { intros h x1 x2 e,
    rw ←h x1, 
    rw ←h x2, 
    rw e },
end

-- Prueba
-- ======

/-
α : Type u,
_inst_1 : inhabited α,
β : Type v,
f : α → β
⊢ injective f ↔ left_inverse (inverse f) f
  >> split,
| ⊢ injective f → left_inverse (inverse f) f
|   >> { intros h y,
| h : injective f,
| y : α
| ⊢ inverse f (f y) = y
|   >>   apply h,
| ⊢ f (inverse f (f y)) = f y
|   >>   apply inverse_spec,
| ⊢ ∃ (x : α), f x = f y
|   >>   use y },
⊢ left_inverse (inverse f) f → injective f
  >> { intros h x1 x2 e,
h : left_inverse (inverse f) f,
x1 x2 : α,
e : f x1 = f x2
⊢ x1 = x2
  >>   rw ←h x1,
⊢ inverse f (f x1) = x2 
  >>   rw ←h x2, 
⊢ inverse f (f x1) = inverse f (f x2)
  >>   rw e },
no goals
-/

-- 2ª demostración
-- ===============

example : injective f ↔ left_inverse (inverse f) f  :=
⟨λ h y, h (inverse_spec _ ⟨y, rfl⟩), 
 λ h x1 x2 e, by rw [←h x1, ←h x2, e]⟩

