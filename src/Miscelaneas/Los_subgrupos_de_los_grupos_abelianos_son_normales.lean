import tactic

namespace paulo

class group (G : Type) extends has_mul G, has_one G, has_inv G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

variables {G: Type} [group G]

namespace group

def is_abelian (G : Type) [group G] :=
∀ (a b : G), a * b = b * a

structure subgroup (G : Type) [group G] :=
(carrier : set G)
(one_mem' : (1 : G) ∈ carrier)
(mul_mem' {x y} : x ∈ carrier → y ∈ carrier → x * y ∈ carrier)
(inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier)

variables (H : subgroup G)

instance : has_mem G (subgroup G) := ⟨λ m H, m ∈ H.carrier⟩

instance : has_coe (subgroup G) (set G) := ⟨λ H, H.carrier⟩

@[simp] lemma mem_carrier
  {g : G}
  : g ∈ H.carrier ↔ g ∈ H :=
by refl

theorem one_mem :
  (1 : G) ∈ H :=
by apply H.one_mem'

/-- A subgroup is closed under multiplication. -/
theorem mul_mem
  {x y : G}
  : x ∈ H → y ∈ H → x * y ∈ H :=
by apply H.mul_mem'

/-- A subgroup is closed under inverse -/
theorem inv_mem
  {x : G}
  : x ∈ H → x⁻¹ ∈ H :=
by apply H.inv_mem'

@[simp] lemma mem_coe
  {g : G}
  : g ∈ (↑H : set G) ↔ g ∈ H :=
by refl

namespace subgroup

def is_normal_subgroup := ∀ (g : G), ∀ (h : H), g*h*g⁻¹ ∈ H

lemma abelian_subgroups_normal
  {G₁ : Type}
  [group G₁]
  (hyp : is_abelian G₁)
  (H₁ : subgroup G₁)
  : is_normal_subgroup H₁ :=
begin
  intros g h,
  unfold is_abelian at hyp,
  rw hyp,
  rw ← mul_assoc,
  rw mul_left_inv,
  rw one_mul,
  cases h with actual_h h_proof,
  exact h_proof,
end

end subgroup

end group

end paulo
