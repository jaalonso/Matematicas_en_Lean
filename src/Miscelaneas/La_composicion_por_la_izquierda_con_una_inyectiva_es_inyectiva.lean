-- La_composicion_por_la_izquierda_con_una_inyectiva_es_inyectiva.lean
-- La composición por la izquierda con una inyectiva es una operación inyectiva
-- José A. Alonso Jiménez
-- Sevilla, 11 de agosto de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Sean f₁ y f₂ funciones de X en Y y g una función de X en Y. Demostrar
-- que si g es inyectiva y g ∘ f₁ = g ∘ f₂, entonces f₁ = f₂.
-- ---------------------------------------------------------------------

import tactic

variables {X Y Z : Type*}
variables {f₁ f₂ : X → Y}
variable  {g : Y → Z}

example
  (hg : function.injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
begin
  funext,
  apply hg,
  calc g (f₁ x)
       = (g ∘ f₁) x : rfl
   ... = (g ∘ f₂) x : congr_fun hgf x
   ... = g (f₂ x)   : rfl,
end

example
  (hg : function.injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
begin
  funext,
  apply hg,
  exact congr_fun hgf x,
end

lemma function.injective.comp_left
  (hg : function.injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
begin
  refine funext (λ i, hg _),
  exact congr_fun hgf i,
end

lemma function.injective.comp_left2
  (hg : function.injective g)
  : function.injective ((∘) g : (X → Y) → (X → Z)) :=
λ f₁ f₂ hgf, funext $ λ i, hg (congr_fun hgf i : _)
