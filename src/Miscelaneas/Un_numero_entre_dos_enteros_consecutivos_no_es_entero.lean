-- Un_numero_entre_dos_enteros_consecutivos_no_es_entero.lean
-- Un número entre dos enteros consecutivos no es entero
-- José A. Alonso Jiménez
-- Sevilla, 10 de agosto de 2021
-- ---------------------------------------------------------------------

import algebra.ordered_ring
import data.int.cast

lemma num_btw_integers_not_integer
  (R : Type*) [linear_ordered_ring R]
  (a: R)
  (n m: ℤ)
  (h : a < m + 1)
  (h₀ : (m : R) < a)
  : a ≠ n :=
begin
  cases le_or_lt n m with n0 n1,
  { have : (n : R) ≤ m,
    { exact_mod_cast n0, },
    exact (lt_of_le_of_lt this h₀).ne', },
  { have : (m : R) + 1 ≤ n,
    { assumption_mod_cast, },
    exact (lt_of_lt_of_le h this).ne, },
end

lemma num_btw_integers_not_integer2
  (R : Type*) [linear_ordered_ring R]
  (a: R)
  (n m: ℤ)
  (h : a < m + 1)
  (h₀ : (m : R) < a)
  : a ≠ n :=
begin
  rintro rfl,
  norm_cast at h h₀,
  exact not_le_of_lt h₀ (int.lt_add_one_iff.1 h),
end
