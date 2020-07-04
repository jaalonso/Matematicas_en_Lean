import tactic

open_locale classical big_operators

open finset

lemma prod_finset_distinct_inv
  {α : Type*} [comm_group α] 
  {s : finset α}
  (h1 : ∀ x ∈ s, x⁻¹ ∈ s) 
  (h2 : ∀ x ∈ s, x⁻¹ ≠ x)
  : ∏ x in s, x = 1 :=
begin
  apply @prod_involution _ _ _ _ _ (λ a ha, a⁻¹),
  { intros, rw mul_inv_self },
  { intros, apply h2, assumption },
  { intros, simp, },
  { intros, apply h1, assumption, },
end
