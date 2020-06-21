import data.real.basic

variables (f g : ℝ → ℝ)

-- 1ª demostración
example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f x + g x) :=
begin
  intros a b aleb,
  apply add_le_add,
  apply mf aleb,
  apply mg aleb
end

-- 2ª demostración
example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f x + g x) :=
λ a b aleb, add_le_add (mf aleb) (mg aleb)

-- Nota: Se puede iniciar la prueba con
--    λ a b aleb, _
-- situarse en _, pulsar C-c SPC y elegir library_search. Automáticamente, se
-- completa la prueba.
