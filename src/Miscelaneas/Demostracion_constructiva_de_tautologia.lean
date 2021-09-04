-- Demostrar, en la lógica intuicionista, (P → (P → Q)) → ((P → Q) → P) → Q

variables (P Q :  Prop)

example : (P → (P → Q)) → ((P → Q) → P) → Q :=
begin
  intros f g,
  let h := λ R, f R R,
  exact f (g h) (g h),
end

example : (P → (P → Q)) → ((P → Q) → P) → Q :=
begin
  intros f g,
  exact f (g (λ R, f R R)) (g (λ R, f R R)),
end

example : (P → (P → Q)) → ((P → Q) → P) → Q :=
begin
  intros f g,
  have h1 : P → Q := λ R, f R R,
  have h2 : P     := g h1,
  exact f h2 h2,
end

example : (P → (P → Q)) → ((P → Q) → P) → Q :=
λ f g, f (g (λ R, f R R)) (g (λ R, f R R))

example : (P → (P → Q)) → ((P → Q) → P) → Q :=
λ f g, let h : P → Q := λ h, f h h in h (g h)
