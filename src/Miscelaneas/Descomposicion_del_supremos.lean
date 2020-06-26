import tactic

lemma supr_split 
  {α ι : Type*} 
  [complete_lattice α] 
  (f : ι → α) 
  (p : ι → Prop) :
  (⨆ i, f i) = (⨆ i (h : p i), f i) ⊔ (⨆ i (h : ¬ p i), f i) :=
begin
  have := @supr_union _ _ _ f {i | p i} {i | ¬ p i},
  dsimp at this, 
  rw ← this,
  clear this,
  have : ∀ x, (p x ∨ ¬ p x) ↔ true, 
    { tauto! },
  congr, 
  dsimp,
  ext, 
  rw this, 
  simp,
end

lemma supr_split_single 
  {α ι : Type*} 
  [complete_lattice α] 
  (f : ι → α) 
  (i₀ : ι) :
  (⨆ i, f i) = f i₀ ⊔ (⨆ i (h : i ≠ i₀), f i) :=
begin
  rw supr_split,
  swap, 
    { exact (λ x, x = i₀) },
  congr, 
  simp,
end

lemma supr_split_single_2 
  {α ι : Type*} 
  [complete_lattice α] 
  (f : ι → α) 
  (i₀ : ι) :
  (⨆ i, f i) = f i₀ ⊔ (⨆ i (h : i ≠ i₀), f i) :=
begin
  by convert supr_split _ _; simp
end
