-- En el artículo "Single axioms for groups and abelian groups with
-- various operations" https://bit.ly/3kMBlA0 de McCune se demuestra que
-- el siguiente axioma caracteriza a los grupos
--    (x * (y * (((z * z⁻¹) * (u * y)⁻¹) * x))⁻¹) = u

import tactic

class mccune_group (α : Type*) extends has_mul α, has_inv α, inhabited α :=
(mccune (x y z u : α) : x * (y * (((z * z⁻¹) * (u * y)⁻¹) * x))⁻¹ = u)

namespace mccune_group
variables {α : Type*} [mccune_group α] (x y z u w v : α)

lemma l5 : x * (y * (z * z⁻¹ * (u * y)⁻¹ * x))⁻¹ = u := mccune _ _ _ _

lemma l7 : x * (y * y⁻¹ * (z * u)⁻¹ * (v * v⁻¹) * (z * x))⁻¹ = u :=
by simpa [l5 (v * v⁻¹)] using l5 x (y * y⁻¹ * (z * u)⁻¹ * (v * v⁻¹)) v u

lemma l9 : x * (y * (z * z⁻¹) * (u * x))⁻¹ = v * v⁻¹ * (y * u)⁻¹ * (w * w⁻¹) :=
by simpa [l5 (w * w⁻¹)] using l7 x w u (v * v⁻¹ * (y * u)⁻¹ * (w * w⁻¹)) z

lemma l10 : y * y⁻¹ * (z * z⁻¹ * (u * x)⁻¹ * u)⁻¹ * (v * v⁻¹) = x :=
by simpa [l9 _ _ _ u v y] using l7 x z u x z

lemma l12 : x * x⁻¹ * y⁻¹⁻¹ * (z * z⁻¹) = y :=
by simpa [l10] using l10 y x x (y * y⁻¹ * (y * y⁻¹)⁻¹) z

lemma l14 : (x * x⁻¹) * (y * z)⁻¹ = u * u⁻¹ * (y * z)⁻¹ := -- [10 -> 5]
begin
  convert l5 _ _ _ _,
  rw l10,
  exact x,
end

lemma l15 : (x * x⁻¹) * y⁻¹ = (z * z⁻¹) * y⁻¹ :=
by simpa [l12] using l14 x ((x * x⁻¹) * y⁻¹⁻¹) (z * z⁻¹) z

lemma l17 : u * u⁻¹ = v * v⁻¹ := -- [15 → 5 : 5]
begin
  rw ←l5 u u⁻¹ u (v * v⁻¹),
  rw l15 v _,
  rw l5,
end

instance : has_one α := ⟨default α * (default α)⁻¹⟩

@[simp] lemma l17' : u * u⁻¹ = 1 := l17 _ _

lemma l10' : (1 * ((1 * (u * x)⁻¹) * u)⁻¹) * 1 = x := l10 _ _ _ _ _

lemma l20' : (1 * (1*z)⁻¹)*1 = z⁻¹ :=
begin
  convert l10' _ _,
  rw l17',
  rw l17',
end

lemma l5' : x * (y * ((1 * (u * y)⁻¹) * x))⁻¹ = u := l5 _ _ _ _

lemma l22' : x * (y⁻¹ * (1 * x))⁻¹ = y := -- [17 → 5]
by { convert l5' _ _ y, simp }

lemma l7' : x * (((1 * (z * u)⁻¹) * 1) * (z * x))⁻¹ = u := l7 _ _ _ _ _

lemma l25' : x * (1⁻¹⁻¹ * (w * x))⁻¹ = w⁻¹ := -- [19 → 7:20]
begin
  convert l7' _ _ _,
  rw l17',
  convert (l20' _).symm,
  simp,
end

lemma l32' : 1⁻¹ * (y⁻¹ * 1)⁻¹ = y := -- [17 → 22]
begin
  convert l22' (1 : α)⁻¹ y,
  simp
end

lemma l34' : x⁻¹ * (1⁻¹⁻¹ * 1)⁻¹ = x⁻¹ := by simpa using l25' x⁻¹ x

lemma l36' : (1 * (x * 1⁻¹⁻¹)⁻¹)⁻¹ = x :=
begin
  convert l5' _ _ _,
  rw l25',
  exact x
end

lemma l44' : x * (1⁻¹⁻¹ * 1)⁻¹ = x := by simpa [l36'] using l34' (1 * (x * 1⁻¹⁻¹)⁻¹)
lemma l48' : (1 : α)⁻¹⁻¹ * 1 = 1 := by simpa using (l44' ((1 : α)⁻¹⁻¹ * 1)).symm
lemma l52' : x * 1⁻¹ = x := by simpa [l48'] using l44' x
lemma l57' : (1⁻¹ * u)⁻¹⁻¹ = u := by simpa [l52', l20'] using l10' u 1⁻¹

lemma l62' : (x⁻¹ * 1)⁻¹ = x⁻¹⁻¹ :=
by simpa [l32'] using (l57' (x⁻¹ * 1)⁻¹).symm

lemma l76' : (x * 1)⁻¹ = x⁻¹ := by simpa [l57'] using l62' (1⁻¹ * x)⁻¹

lemma l88' : 1⁻¹ * x⁻¹⁻¹ = x :=
by simpa [l76'] using l32' x

@[simp] lemma l116' : y * 1 = y :=
begin
  have := l88' (y * 1),
  rw l76' at this,
  rw l88' at this,
  exact this.symm
end

@[simp] lemma one_inv_inv : (1 : α)⁻¹⁻¹ = 1 :=
by simpa using l48'

@[simp] lemma one_inv : (1 : α)⁻¹ = 1 :=
by simpa using l88' (1 : α)

lemma l92' : (1 * y⁻¹)⁻¹ = y :=
by simpa using l36' y

lemma l126' : (y * z) * z⁻¹ = y :=
begin
  have := l5' ((1 : α) * (y * z)⁻¹)⁻¹ z y,
  rw l17' at this,
  simpa [l92'] using this,
end

lemma l201 : x * y⁻¹⁻¹ = x * y :=
by simpa [l126' x y] using l126' (x * y) y⁻¹

@[simp] lemma l207' : 1 * z = z :=
by simpa [l201] using l126' z z⁻¹

@[simp] lemma l227 : y⁻¹⁻¹ = y :=
by simpa using l201 1 y

@[simp] lemma inv_mul : x⁻¹ * x = 1 :=
by simpa using l17' x⁻¹

lemma l229 : (z * x)⁻¹ = x⁻¹ * z⁻¹ := -- 126->25:227,207
by simpa [l126'] using (l25' x⁻¹ (z * x)).symm

lemma thingy : x * (x⁻¹ * z) = z := -- [126->5:207,229,229,227,227]
begin
  have := l5' x z⁻¹ z,
  simp only [one_inv, l17', l207'] at this,
  rw [l229, l227] at this,
  exact this,
end

lemma l239 : x * ((x⁻¹ * u) * y) = u * y := -- [126->5:207,229,229,227,227]
by simpa [l229, l126'] using l5' x y⁻¹ (u * y)

lemma l260 : (x * y) * z = x * (y * z) := -- [215->215:229,229,229,227,227,239]
begin
  rw ←l239 x⁻¹ z y,
  rw thingy,
  simp
end

instance : group α :=
{ mul_assoc := l260,
  one_mul := by simp,
  mul_one := by simp,
  mul_left_inv := λ x, inv_mul _,
  ..(by apply_instance : has_one α),
  ..(by apply_instance : has_mul α),
  ..(by apply_instance : has_inv α) }

end mccune_group
