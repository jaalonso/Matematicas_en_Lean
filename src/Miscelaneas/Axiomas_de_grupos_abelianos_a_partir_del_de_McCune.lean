-- En el artículo "Single axioms for groups and abelian groups with
-- various operations" https://bit.ly/3kMBlA0 de McCune se demuestra que
-- el siguiente axioma caracteriza a los grupos
--    (x * (y * (((z * z⁻¹) * (u * y)⁻¹) * x))⁻¹) = u

import tactic

class mccune_comm_group (α : Type*) extends has_mul α, has_inv α, inhabited α :=
(mccune (x y z : α) : x * y * z * (x * z)⁻¹ = y)

namespace mccune_comm_group
variables {α : Type*} [mccune_comm_group α] (x y z u v w : α)

lemma l10 : x * y * (z * x * u * y)⁻¹ = (z * u)⁻¹ :=
by simpa [mccune] using mccune (z * x * u) (z * u)⁻¹ y

lemma l12 : x * (y * x * (y * z)⁻¹)⁻¹ = z := by simpa [mccune] using mccune (y * x) z (y * z)⁻¹
lemma l16 : x * (y * z)⁻¹ * x⁻¹ = (y * z)⁻¹ := by simpa [mccune] using l10 x (y * z)⁻¹ y z
lemma l18 : (y * (z * (y * z * x)⁻¹))⁻¹ = x :=
by simpa [l10] using l12 (z * (y * z * x)⁻¹) (y * z) x
lemma l23 : (x * y * (x * (y * z))⁻¹)⁻¹ = z := by simpa [l10] using l18 z (x * y) (y * z)
lemma l37 : x * y * x⁻¹ = y := by simpa [l23] using l16 x (x * x) (x * (x * y))⁻¹
lemma l39 : (z * y * (z * x)⁻¹)⁻¹ = x * y⁻¹ := by simpa [l12] using (l16 y (z * y) (z * x)⁻¹).symm
lemma l41 : x * (y * x * z)⁻¹ = (y * z)⁻¹ := by simpa [mccune] using l16 (y * x * z) y z
lemma l43 : x * (z * x⁻¹) = z := by simpa [l39] using l12 x x z
lemma l51 : (x * (x * z)⁻¹)⁻¹ = z := by simpa [l41] using l18 z x x
lemma l53 : x * (y * x)⁻¹ = y⁻¹ := by simpa [l37] using l37 (y * x) y⁻¹
lemma l55 : (y * z)⁻¹ = y⁻¹ * z⁻¹ := by simpa [l53, l37] using (l10 z (y * z)⁻¹ y z).symm
lemma l58 : x * y * z * x⁻¹ * y⁻¹ = z := by simpa [l37] using mccune (x * y) z x⁻¹
lemma l60 : x * (y⁻¹ * y⁻¹⁻¹) = x := by simpa [l37, l55] using mccune y x y⁻¹
lemma l64 : x⁻¹ * (x⁻¹⁻¹ * y⁻¹⁻¹) = y := by simpa [l55] using l51 x y
@[simp] lemma l85 : x⁻¹⁻¹ = x := by simpa [l43] using l64 x x
lemma l92 : x⁻¹ * (x * y) = y := by simpa using l64 x y
lemma l94 : x * (y⁻¹ * y) = x := by simpa using l60 x y
lemma l101 : x * (x⁻¹ * y) = y := by simpa using l92 x⁻¹ y
lemma l108 : x * y = y * x := by simpa [l92] using l37 y⁻¹ (y * x)
lemma l114 : x * (y * y⁻¹) = x := by simpa using l94 x y⁻¹
lemma l136 : x * x⁻¹ = y * y⁻¹ := by simpa [l114] using l101 x (y * y⁻¹)
lemma l172 : z * x * y * z⁻¹ = x * y := by simpa [l58] using (l43 x (z * x * y * z⁻¹)).symm
lemma l184 : x * y * z = z * x * y := by simpa [l92 z x] using l172 (z * x) y z⁻¹
lemma l244 : x * y * z = x * (y * z) := by simpa [l184 y] using (l108 x (y * z)).symm

/-- Every McCune comm group is a comm group. -/
instance : comm_group α :=
{ mul_assoc := l244,
  one := default α * (default α)⁻¹,
  mul_one := λ x, l114 x _,
  mul_comm := l108,
  mul_left_inv := λ x, (l108 _ x).trans (l136 x (default α)),
  one_mul := λ x, by rw [l108, l114],
  ..(by apply_instance : has_mul α),
  ..(by apply_instance : has_inv α) }

end mccune_comm_group
