-- Representación decimal
-- ======================

import data.nat.digits
import data.list.range

lemma list.map_with_index_core_eq
  {α β : Type*}
  (l : list α)
  (f : ℕ → α → β) (n : ℕ)
  : l.map_with_index_core f n = l.map_with_index (λ i a, f (i + n) a) :=
begin
  induction l with hd tl hl generalizing f n,
  { simp [list.map_with_index, list.map_with_index_core] },
  { rw [list.map_with_index],
    simp [list.map_with_index_core, hl, add_left_comm, add_assoc, add_comm] }
end

@[simp]
lemma list.map_uncurry_zip_eq_zip_with
  {α β γ : Type*}
  (f : α → β → γ)
  (l : list α)
  (l' : list β)
  : list.map (function.uncurry f) (l.zip l') = list.zip_with f l l' :=
begin
  induction l with hd tl hl generalizing l',
  { simp },
  { cases l' with hd' tl',
    { simp },
    { simp [hl] } }
end

lemma list.zip_with_map_left
  {α β γ δ : Type*}
  (f : α → β → γ)
  (g : δ → α)
  (l : list δ)
  (l' : list β)
  : list.zip_with f (l.map g) l' = list.zip_with (f ∘ g) l l' :=
begin
  induction l with hd tl hl generalizing l',
  { simp },
  { cases l' with hd' tl',
    { simp },
    { simp [hl] } }
end

lemma list.zip_with_map_right
  {α β γ δ : Type*}
  (f : α → β → γ)
  (l : list α)
  (g : δ → β)
  (l' : list δ)
  : list.zip_with f l (l'.map g) = list.zip_with (λ x, f x ∘ g) l l' :=
begin
  induction l with hd tl hl generalizing l',
  { simp },
  { cases l' with hd' tl',
    { simp },
    { simp [hl] } }
end

lemma list.map_with_index_eq_enum_map_uncurry
  {α β : Type*}
  (l : list α)
  (f : ℕ → α → β)
  : l.map_with_index f = l.enum.map (function.uncurry f) :=
begin
  induction l with hd tl hl generalizing f,
  { simp [list.map_with_index, list.map_with_index_core, list.enum_eq_zip_range] },
  { rw [list.map_with_index, list.map_with_index_core, list.map_with_index_core_eq, hl],
    simp [list.enum_eq_zip_range, list.range_succ_eq_map, list.zip_with_map_left] }
end

@[simp]
lemma list.sum_zip_with_distrib_left
  {α β : Type*}
  (f : α → β → ℕ)
  (n : ℕ)
  (l : list α)
  (l' : list β)
  : (list.zip_with (λ x y, n * f x y) l l').sum = n * (l.zip_with f l').sum :=
begin
  induction l with hd tl hl generalizing f n l',
  { simp },
  { cases l' with hd' tl',
    { simp, },
    { simp [hl, mul_add] } }
end

lemma aux
  (b : ℕ)
  (l : list ℕ)
  : (list.zip_with ((λ (i a : ℕ), a * b ^ i) ∘ nat.succ) (list.range l.length) l).sum =
     b * (list.zip_with (λ i a, a * b ^ i) (list.range l.length) l).sum :=
begin
  suffices : list.zip_with (((λ (i a : ℕ), a * b ^ i) ∘ nat.succ)) (list.range l.length) l =
      list.zip_with (λ i a, b * (a * b ^ i)) (list.range l.length) l,
    { simp [this] },
  congr,
  ext,
  simp [pow_succ],
  ring
end

lemma mwe
  (b n: ℕ)
  : list.sum ((nat.digits b n).map_with_index (λ i a, a * b ^ i)) = n :=
begin
  conv {
      to_rhs,
      rw ← nat.of_digits_digits b n,
    },
  rw [list.map_with_index_eq_enum_map_uncurry, list.enum_eq_zip_range,
      list.map_uncurry_zip_eq_zip_with, nat.of_digits_eq_foldr b],
  induction b.digits n with hd tl hl,
  { simp },
  { simp [list.range_succ_eq_map, list.zip_with_map_left, aux, hl] }
end

-- Referencia
-- ==========

-- Yakov Pechersky "How to work on base representations and lists?"
-- https://bit.ly/3r8RPCj
