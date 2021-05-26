-- Esquema de inducción
-- ====================

import tactic

-- 1ª demostración
example
  {α : Type}
  {P : α → Prop}
  (next : α → α)
  (s : α)
  (h : ∀ a : α, P a → P (next a))
  (hs : P s)
  : ∃ f : ℕ → α, ∀ n : ℕ, P (f n) :=
begin
  let f : ℕ → α := λ n, nat.rec_on n s (λ m, next),
  use f,
  intro n,
  induction n with n hn,
  { exact hs },
  { apply h,
    exact hn }
end

-- 2ª demostración
example
  {α : Type}
  {P : α → Prop}
  (next : α → α)
  (s : α)
  (h : ∀ a : α, P a → P (next a))
  (hs : P s)
  : ∃ f : ℕ → α, ∀ n : ℕ, P (f n) :=
begin
  set f : ℕ → α := λ n, nat.rec_on n s (λ n, next) with hf,
  use f,
  intro n,
  induction n with n hn,
  { rw hf,
    dsimp only,
    exact hs },
  { apply h,
    rw hf at hn,
    dsimp only at hn,
    exact hn, },
end
