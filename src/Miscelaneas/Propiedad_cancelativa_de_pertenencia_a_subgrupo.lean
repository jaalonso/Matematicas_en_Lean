import tactic
import group_theory.subgroup

-- 1ª demostración
example
  {G : Type*} [comm_group G] 
  (s : subgroup G) 
  {g a : G}
  (h₁ : a ∈ s)
  (h₂ : g * a ∈ s)
  : g ∈ s:=
begin
  have a_inv_in_s : a⁻¹ ∈ s, 
    by {rw subgroup.inv_mem_iff, exact h₁},
  suffices mess : g*(a⁻¹)⁻¹*a⁻¹ ∈ s, 
    by {rw inv_mul_cancel_right at mess, exact mess},
  have h₃ : g*a*a⁻¹ = g*(a⁻¹)⁻¹*a⁻¹ , 
    by norm_num,
  have h₄ : g*a*a⁻¹∈ s, 
    by exact s.mul_mem(h₂)(a_inv_in_s),
  rw h₃ at h₄,
  exact h₄,
end

-- 2ª demostración
example
  {G : Type*} [comm_group G] 
  (s : subgroup G) 
  {g a : G}
  (h₁ : a ∈ s)
  (h₂ : g * a ∈ s)
  :  g ∈ s:=
begin
  -- library_search,
  exact (subgroup.mul_mem_cancel_right s h₁).mp h₂
end


