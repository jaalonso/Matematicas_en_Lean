variables {α : Type*} (r s t : set α)

-- 1ª demostración
example : r ⊆ s → s ⊆ t → r ⊆ t :=
begin
  intros rs st x xr,
  apply st,
  apply rs,
  exact xr 
end

-- 2ª demostración
example : r ⊆ s → s ⊆ t → r ⊆ t :=
λ rs st x xr, st (rs xr)
