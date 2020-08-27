import .Funcion_inversa

universes u v                          
variables {α : Type u} [inhabited α]   
variables {β : Type v}                 
variable  f : α → β
variable  g : β → α
variable  x : α

open set function

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que g es la inversa por la derecha de f syss
--    ∀ x, f (g x) = x :=
-- ----------------------------------------------------------------------

example : right_inverse g f ↔ ∀ x, f (g x) = x :=
begin
  rw function.right_inverse,
  rw left_inverse,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que las siguientes condiciones son equivalentes:
-- 1. f es suprayectiva
-- 2. right_inverse (inverse f) f
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : surjective f ↔ right_inverse (inverse f) f :=
begin
  split,
  { intros h y,
    apply inverse_spec,
    apply h },
  { intros h y,
    use (inverse f y),
    apply h },
end

-- Prueba
-- ======

/-
α : Type u,
_inst_1 : inhabited α,
β : Type v,
f : α → β
⊢ surjective f ↔ right_inverse (inverse f) f
  >> split,
| ⊢ surjective f → right_inverse (inverse f) f
|   >> { intros h y,
| h : surjective f,
| y : β
| ⊢ f (inverse f y) = y
|   >>   apply inverse_spec,
| ⊢ ∃ (x : α), f x = y
|   >>   apply h },
⊢ right_inverse (inverse f) f → surjective f
  >> { intros h y,
h : right_inverse (inverse f) f,
y : β
⊢ ∃ (a : α), f a = y
  >>   use (inverse f y),
⊢ f (inverse f y) = y
  >>   apply h },
no goals
-/

-- 2ª demostración
-- ===============

example : surjective f ↔ right_inverse (inverse f) f :=
⟨λ h y, inverse_spec _ (h _), 
 λ h y, ⟨inverse f y, h _⟩⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que f es suprayectiva syss tiene una inversa por
-- la izquierda.
-- ----------------------------------------------------------------------

example : surjective f ↔ ∃ g, right_inverse g f :=
begin
  split,
  { intro h,
    dsimp [surjective] at h, 
    choose g hg using h,
    use g,
    exact hg },
  { rintro ⟨g, hg⟩,
    intros b,
    use g b,
    exact hg b },
end

-- Prueba
-- ======

/-
α : Type u,
_inst_1 : inhabited α,
β : Type v,
f : α → β
⊢ surjective f ↔ ∃ (g : β → α), right_inverse g f
  >> split,
| ⊢ surjective f → (∃ (g : β → α), right_inverse g f)
|   >> { intro h,
| h : surjective f
| ⊢ ∃ (g : β → α), right_inverse g f
|   >>   dsimp [surjective] at h,
| h : ∀ (b : β), ∃ (a : α), f a = b
| ⊢ ∃ (g : β → α), right_inverse g f 
|   >>   choose g hg using h,
| g : β → α,
| hg : ∀ (b : β), f (g b) = b
| ⊢ ∃ (g : β → α), right_inverse g f
|   >>   use g,
| ⊢ right_inverse g f
|   >>   exact hg },
⊢ (∃ (g : β → α), right_inverse g f) → surjective f
  >> { rintro ⟨g, hg⟩,
g : β → α,
hg : right_inverse g f
⊢ surjective f
  >>   intros b,
b : β
⊢ ∃ (a : α), f a = b
  >>   use g b,
⊢ f (g b) = b
  >>   exact hg b },
no goals
-/

-- Comentantarios:
-- 1. La táctica (dsimp [e] at h) simplifica la hipótesis h con la
--    definición de e.
-- 2. La táctica (choose g hg using h) si h es de la forma 
--    (∀ (b : β), ∃ (a : α), f a = b) quita la hipótesis h y añade las
--     hipótesis (g : β → α) y (hg : ∀ (b : β), f (g b) = b).

