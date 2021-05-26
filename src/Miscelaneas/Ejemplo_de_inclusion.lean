import tactic
import data.set.lattice

-- 1ª demostración
example
  [α : Type]
  (S Γ : set α)
  (φ : α)
  (H : φ ∉ S)
  (H' : S ⊆ Γ ∪ {φ})
  : S ⊆ Γ :=
begin
  intros x hs,
  have := H' hs,
  rw set.mem_union at this,
  apply this.resolve_right,
  rw set.mem_singleton_iff,
  rintro rfl,
  contradiction,
end

-- 2ª demostración
example
  [α : Type]
  (S Γ : set α)
  (φ : α)
  (H : φ ∉ S)
  (H' : S ⊆ Γ ∪ {φ})
  : S ⊆ Γ :=
begin
  intros x hs,
  have := H' hs,
  finish,
end
