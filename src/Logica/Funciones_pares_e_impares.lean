import data.real.basic

variables (f g : ℝ → ℝ)

def even (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)
def odd  (f : ℝ → ℝ) : Prop := ∀ x, f x = - f (-x)

example (ef : even f) (eg : even g) : even (λ x, f x + g x) :=
begin
  intro x,
  calc
    (λ x, f x + g x) x = f x + g x       : rfl
                   ... = f (-x) + g (-x) : by rw [ef, eg]
end

example (of : odd f) (og : odd g) : even (λ x, f x * g x) :=
begin
  intro x,
  calc
    (λ x, f x * g x) x 
        = f x * g x               : rfl
    ... = -f (-x) * -g (-x)       : by rw [of, og]
    ... = f (-x) * g (-x)         : by rw neg_mul_neg 
    ... = ((λ x, f x * g x) (-x)) : rfl
end

example (ef : even f) (og : odd g) : odd (λ x, f x * g x) :=
begin
  intro x,
  calc
    (λ x, f x * g x) x 
        = f x * g x                : rfl
    ... = f (-x) * -g (-x)         : by rw [ef, og]
    ... = -(f (-x) * g (-x))       : by rw neg_mul_eq_mul_neg
    ... = -((λ x, f x * g x) (-x)) : rfl
end

example (ef : even f) (og : odd g) : even (λ x, f (g x)) :=
begin
  intro x,
  calc
    (λ x, f (g x)) x 
        = f (g x)               : rfl
    ... = f (-g (-x))           : by rw og
    ... = f (g (-x))            : by rw ← ef
    ... = ((λ x, f (g x)) (-x)) : rfl
end

