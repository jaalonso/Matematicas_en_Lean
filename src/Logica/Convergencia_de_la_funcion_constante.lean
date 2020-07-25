-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que, para todo a ∈ ℝ, la función constante 
--    s(x) = a
-- converge a a.
-- ----------------------------------------------------------------------

import .Definicion_de_convergencia

lemma converges_to_const 
  (a : ℝ)
  : converges_to (λ x : ℕ, a) a :=
begin
  intros ε εpos,
  use 0,
  intros n nge, 
  dsimp,
  rw sub_self, 
  rw abs_zero,
  exact εpos,
end

-- Prueba
-- ======

/-
a : ℝ
⊢ converges_to (λ (x : ℕ), a) a
  >> intros ε εpos,
a ε : ℝ,
εpos : ε > 0
⊢ ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → abs ((λ (x : ℕ), a) n - a) < ε
  >> use 0,
⊢ ∀ (n : ℕ), n ≥ 0 → abs ((λ (x : ℕ), a) n - a) < ε
  >> intros n nge, 
n : ℕ,
nge : n ≥ 0
⊢ abs ((λ (x : ℕ), a) n - a) < ε
  >> dsimp,
⊢ abs (a - a) < ε
  >> rw sub_self,
⊢ abs 0 < ε 
  >> rw abs_zero,
⊢ abs 0 < ε
  >> exact εpos,
no goals
-/

-- Comentario: Se han usado los lemas
-- + sub_self a : a - a = 0 
-- + abs_zero : abs 0 = 0 

variables (a : ℝ)
#check @sub_self _ _ a 
#check @abs_zero _ _
