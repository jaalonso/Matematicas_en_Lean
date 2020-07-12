-- ---------------------------------------------------------------------
-- Ejercicio . Demostrar que la composición de funciones suprayectivas
-- es suprayectiva.
-- ----------------------------------------------------------------------


import tactic

open function

variables {α : Type*} {β : Type*} {γ : Type*}
variables {f : α → β} {g : β → γ} 

example 
  (surjg : surjective g) 
  (surjf : surjective f) 
  : surjective (λ x, g (f x)) :=
begin
  intro x,
  cases surjg x with y hy,
  cases surjf y with z hz,
  use z,
  change g (f z) = x,
  rw hz,
  exact hy,
end

-- La prueba es
-- 
-- α : Type u_1,
-- β : Type u_2,
-- γ : Type u_3,
-- f : α → β,
-- g : β → γ,
-- surjg : surjective g,
-- surjf : surjective f
-- ⊢ surjective (λ (x : α), g (f x))
--    >> intro x,
-- x : γ
-- ⊢ ∃ (a : α), (λ (x : α), g (f x)) a = x
--    >> cases surjg x with y hy,
-- y : β,
-- hy : g y = x
-- ⊢ ∃ (a : α), (λ (x : α), g (f x)) a = x
--    >> cases surjf y with z hz,
-- z : α,
-- hz : f z = y
-- ⊢ ∃ (a : α), (λ (x : α), g (f x)) a = x
--    >> use z,
-- ⊢ (λ (x : α), g (f x)) z = x
--    >> change g (f z) = x,
-- ⊢ g (f z) = x
--    >> rw hz,
-- ⊢ g y = x
--    >> exact hy
-- no goals
