-- La_composicion_por_la_izquierda_con_una_inyectiva_es_inyectiva.lean
-- La composición por la izquierda con una inyectiva es una operación inyectiva
-- José A. Alonso Jiménez
-- Sevilla, 11 de agosto de 2021
-- ---------------------------------------------------------------------

import tactic

example
  {α β γ : Type*}
  {f₁ f₂ : α → β}
  {g : β → γ}
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
  {α β γ : Type*}
  {f₁ f₂ : α → β}
  {g : β → γ}
  (hg : function.injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
begin
  funext,
  apply hg,
  exact congr_fun hgf x,
end

lemma function.injective.comp_left
  {α β γ : Type*}
  {f₁ f₂ : α → β}
  {g : β → γ}
  (hg : function.injective g)
  (hgf : g ∘ f₁ = g ∘ f₂)
  : f₁ = f₂ :=
begin
  refine funext (λ i, hg _),
  exact congr_fun hgf i,
end

lemma function.injective.comp_left2
  {α β γ : Type*}
  {g : β → γ}
  (hg : function.injective g)
  : function.injective ((∘) g : (α → β) → (α → γ)) :=
λ f₁ f₂ hgf, funext $ λ i, hg (congr_fun hgf i : _)
