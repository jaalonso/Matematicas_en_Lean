import tactic

variables (p q r : Prop)

-- 1ª demostración
example : ((p ∨ q) → r) ↔ ((p → r) ∧ (q → r)) :=
or_imp_distrib

-- 2ª demostración
example : ((p ∨ q) → r) ↔ ((p → r) ∧ (q → r)) :=
⟨λ h, ⟨λ hp, h (or.inl hp), 
       λ hq, h (or.inr hq)⟩, 
 λ ⟨hpr, hqr⟩ hpq, hpq.elim hpr hqr⟩

-- 3ª demostración
example : ((p ∨ q) → r) ↔ ((p → r) ∧ (q → r)) :=
begin
  split,
  { intro h,
    split,
    { intro hp,
      exact h (or.inl hp), },
    { intro hq,
      exact h (or.inr hq), }},
  { rintros ⟨hpr, hqr⟩ hpq,
    cases hpq with hp hq,
    { exact hpr hp, },
    { exact hqr hq, }},
end    

