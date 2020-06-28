import tactic

noncomputable theory
open_locale big_operators
open_locale classical

lemma sum_add_induction 
  {α M : Type} 
  [add_comm_monoid M] 
  {p : M → Prop}
  (f : α → M) 
  (s : finset α) 
  (p_add : ∀ a b, p a → p b → p (a + b)) 
  (p_zero : p 0) 
  (p_s : ∀ x ∈ s, p $ f x) 
  : p $ ∑ x in s, f x :=
begin
  induction s using finset.induction with x hx s hs, 
  { simpa },
  { rw finset.sum_insert, 
    swap, 
    { assumption },
    { apply p_add, 
      { apply p_s, 
        simp },
      { apply hs, 
        intros a ha, 
        apply p_s, 
        simp [ha] }}},
end
