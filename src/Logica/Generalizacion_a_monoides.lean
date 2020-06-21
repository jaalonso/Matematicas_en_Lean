import algebra.ordered_group

variables {α : Type*} {R : Type*} [ordered_cancel_add_comm_monoid R]

#check @add_le_add
-- | add_le_add :
-- |  ∀ {α : Type u_3} [_inst_1 : ordered_cancel_add_comm_monoid α] {a b c d : α},
-- |    a ≤ b → c ≤ d → a + c ≤ b + d

def fn_ub (f : α → R) (a : R) : Prop := ∀ x, f x ≤ a

theorem fn_ub_add {f g : α → R} {a b : R}
  (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)
