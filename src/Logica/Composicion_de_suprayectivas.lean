import tactic

open function

variables {α : Type*} {β : Type*} {γ : Type*}
variables {g : β → γ} {f : α → β}

example 
  (surjg : surjective g) 
  (surjf : surjective f) :
  surjective (λ x, g (f x)) :=
begin
  intro x,
  cases surjg x with y hy,
  cases surjf y with z hz,
  use z,
  change g (f z) = x,
  rw hz,
  exact hy
end
