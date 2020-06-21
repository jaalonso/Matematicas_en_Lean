variables {α : Type*} (s : set α)

-- 1ª demostración
example : s ⊆ s :=
by { intros x xs, exact xs }

-- 2ª demostración
example : s ⊆ s := λ x xs, xs

