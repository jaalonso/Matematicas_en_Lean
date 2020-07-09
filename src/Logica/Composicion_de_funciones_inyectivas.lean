-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la composición de funciones inyectivas es
-- inyectiva. 
-- ----------------------------------------------------------------------

import tactic

open function

variables {α : Type*} {β : Type*} {γ : Type*}
variables {f : α → β} {g : β → γ} 

example
  (injg : injective g) 
  (injf : injective f) :
  injective (λ x, g (f x)) :=
begin
  intros x₁ x₂ h,
  apply injf,
  apply injg,
  apply h,
end

-- Su desarrollo es
--
-- α : Type u_1,
-- β : Type u_2,
-- γ : Type u_3,
-- f : α → β,
-- g : β → γ,
-- injg : injective g,
-- injf : injective f
-- ⊢ injective (λ (x : α), g (f x))
--    >> intros x₁ x₂ h,
-- x₁ x₂ : α,
-- h : (λ (x : α), g (f x)) x₁ = (λ (x : α), g (f x)) x₂
-- ⊢ x₁ = x₂
--    >> apply injf,
-- ⊢ f x₁ = f x₂
--    >> apply injg,
-- ⊢ g (f x₁) = g (f x₂)
--    >> apply h,
-- no goals


