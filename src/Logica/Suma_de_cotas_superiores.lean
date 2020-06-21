import data.real.basic

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

variables (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (λ x, f x + g x) (a + b) :=
begin
  intro x,
  -- dsimp,
  change f x + g x ≤ a + b,
  apply add_le_add,
  apply hfa,
  apply hgb
end

-- Notas. 
-- + Nota 1. Con "intro x" se despliega la definición de fn_ub y se introduce 
--   la variable x en el contexto. 
-- + Nota 3. Con "dsimp" se simplifica la definición del lambda. El mismo 
--   efecto se consigue con "change f x + g x ≤ a + b"
