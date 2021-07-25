-- Suma_de_fila_del_triangulo_de_Pascal.lean
-- Suma de fila del triángulo de Pascal
-- José A. Alonso Jiménez
-- Sevilla, 25 de julio de 2021
-- ---------------------------------------------------------------------

import tactic
import data.finset.basic
open finset nat
open_locale big_operators

theorem sum_pascal_row (n : ℕ) :
  ∑ (m : ℕ) in range (n + 1), (choose n m) = 2 ^ n :=
begin
  induction n with d hd,
  { refl },
  { calc ∑ i in range (d + 2), choose (d + 1) i
        = ∑ i in range (d + 1), choose (d + 1) (i + 1) + 1
          : by simp [sum_range_succ']
    ... = ∑ i in range (d + 1), (choose d i + choose d (i+1)) + 1
          : rfl
    ... = ∑ i in range (d + 1), choose d i +
          ∑ i in range (d + 1), choose d (i+1) + 1
          : by rw sum_add_distrib
    ... = 2^d + ∑ i in range (d + 1), choose d (i+1) + 1
          : by rw hd
    ... = 2^d + ∑ i in range d, choose d (i+1) + 1
          : by simp [sum_range_succ]
    ... = 2^d + ∑ i in range (d + 1), choose d i
          : by simp [sum_range_succ', add_assoc]
    ... = 2^d + 2^d
          : by rw hd
    ... = 2*2^d
          : by ring,
  }
end
