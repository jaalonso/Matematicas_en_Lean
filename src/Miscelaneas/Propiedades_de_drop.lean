import tactic
open list

variable {α : Type}

@[simp]
lemma drop_eq_nil_of_le
  {l : list α}
  {k : ℕ}
  (h : length l ≤ k)
  : drop k l = [] :=
by simpa [←length_eq_zero] using nat.sub_eq_zero_of_le h

theorem drop_nil :
  ∀ n, drop n [] = ([] : list α) :=
λ _, list.drop_eq_nil_of_le (nat.zero_le _)
