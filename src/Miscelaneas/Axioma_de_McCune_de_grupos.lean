-- Axioma_de_McCune_de_grupos.lean
-- Axioma de McCune de grupos
-- José A. Alonso Jiménez
-- Sevilla, 23 de julio de 2021
-- ---------------------------------------------------------------------

-- En el artículo "Single axioms for groups and abelian groups with
-- various operations" https://bit.ly/3kMBlA0 de McCune se demuestra que
-- el siguiente axioma caracteriza a los grupos
--    (x * (y * (((z * z⁻¹) * (u * y)⁻¹) * x))⁻¹) = u

import tactic

variables {G : Type} [group G] (x y z u v w : G)

-- 1ª demostración
example :
  x * (y * (((z * z⁻¹) * (u * y)⁻¹) * x))⁻¹ = u :=
  by group

-- 2ª demostración
example :
  x * (y * (((z * z⁻¹) * (u * y)⁻¹) * x))⁻¹ = u :=
calc x * (y * (((z * z⁻¹) * (u * y)⁻¹) * x))⁻¹
     = x * (y * ((1 * (u * y)⁻¹) * x))⁻¹       : by simp
 ... = x * (y * ((u * y)⁻¹ * x))⁻¹             : by simp
 ... = x * (((u * y)⁻¹ * x)⁻¹ * y⁻¹)           : by simp
 ... = x * ((x⁻¹ * ((u * y)⁻¹)⁻¹) * y⁻¹)       : by simp
 ... = x * ((x⁻¹ * (u * y)) * y⁻¹)             : by simp
 ... = (x * x⁻¹) * ((u * y) * y⁻¹)             : by simp only [mul_assoc]
 ... = 1 * ((u * y) * y⁻¹)                     : by simp
 ... = (u * y) * y⁻¹                           : by simp
 ... = u * (y * y⁻¹)                           : by simp
 ... = u * 1                                   : by simp
 ... = u                                       : by simp

-- 3ª demostración
lemma l5 :
  x * (y * (((z * z⁻¹) * (u * y)⁻¹) * x))⁻¹ = u :=
calc x * (y * (((z * z⁻¹) * (u * y)⁻¹) * x))⁻¹
     = x * (y * ((1 * (u * y)⁻¹) * x))⁻¹       : by simp only [mul_inv_self]
 ... = x * (y * ((u * y)⁻¹ * x))⁻¹             : by simp only [one_mul]
 ... = x * (((u * y)⁻¹ * x)⁻¹ * y⁻¹)           : by simp only [mul_inv_rev]
 ... = x * ((x⁻¹ * ((u * y)⁻¹)⁻¹) * y⁻¹)       : by simp only [mul_inv_rev]
 ... = x * ((x⁻¹ * (u * y)) * y⁻¹)             : by simp only [inv_inv]
 ... = (x * x⁻¹) * ((u * y) * y⁻¹)             : by simp only [mul_assoc]
 ... = 1 * ((u * y) * y⁻¹)                     : by simp only [mul_inv_self]
 ... = (u * y) * y⁻¹                           : by simp only [one_mul]
 ... = u * (y * y⁻¹)                           : by simp only [mul_assoc]
 ... = u * 1                                   : by simp only [mul_inv_self]
 ... = u                                       : by simp only [mul_one]

-- =====================================================================
-- § Lema 7                                                           --
-- =====================================================================

lemma l7 :
  x * ((((y * y⁻¹) * (z * u)⁻¹) * (v * v⁻¹)) * (z * x))⁻¹ = u :=
begin
  convert l5 _ _ _ _,
  rw l5,
end

-- =====================================================================
-- § Lema 9                                                           --
-- =====================================================================

lemma l9 :
  (x * ((y * (z * z⁻¹)) * (u * x))⁻¹) = (((v * v⁻¹) *(y * u)⁻¹) * (w * w⁻¹)) :=
begin
  convert l7 _ _ _ _ _,
  rw l5,
end

-- =====================================================================
-- § Lema 10                                                          --
-- =====================================================================

lemma l10 :
  (((y * y⁻¹)*(((z*z⁻¹)*(u*x)⁻¹)*u)⁻¹)*(v*v⁻¹)) = x :=
begin
  rw ←l9,
  apply l7,
  exact x,
  exact z,
end

-- =====================================================================
-- § Lema 12                                                          --
-- =====================================================================

lemma l12 : (((x * x⁻¹)*y⁻¹⁻¹)*(z*z⁻¹))=y :=
begin
  convert l10 _ _ _ _ _,
  rw l10,
  exact x
end

-- =====================================================================
-- § Lema 14                                                          --
-- =====================================================================

lemma l14 : ((x*x⁻¹)*(y*z)⁻¹)=((u*u⁻¹)*(y*z)⁻¹) := -- [10 -> 5]
begin
  convert l5 _ _ _ _,
  rw l10,
  exact x,
end

-- =====================================================================
-- § Lema 15                                                          --
-- =====================================================================

lemma l15 : ((x*x⁻¹)*y⁻¹) = ((z*z⁻¹)*y⁻¹) := -- [12 -> 14 : 12]
begin
  convert l14 _ _ _ _,
  rw l12,
  exact x,
  exact z,
  rw l12,
end

-- =====================================================================
-- § Lema 17                                                          --
-- =====================================================================

lemma l17 : u * u⁻¹ = v * v⁻¹ := -- [15 → 5 : 5]
begin
  rw ←l5 u u⁻¹ u (v * v⁻¹),
  rw l15 v _,
  rw l5,
end

-- =====================================================================
-- § Lema 19                                                          --
-- =====================================================================

lemma l19 : x * x⁻¹ = ((y * y⁻¹) * (z * z⁻¹)⁻¹) := -- [17 → 15]
begin
  rw [l15],
  exact l17 _ _,
end
