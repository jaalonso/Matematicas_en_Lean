variables {α : Type*} [partial_order α]
variables (s : set α) (a b : α)

def set_ub (s : set α) (a : α) := ∀ x, x ∈ s → x ≤ a

example (h : set_ub s a) (h' : a ≤ b) : set_ub s b :=
begin
  intros x xs,
  calc 
    x   ≤ a : (h x xs)
    ... ≤ b : h'
end

