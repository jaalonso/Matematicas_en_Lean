import tactic

-- 1ª definición
def splitAt1 {a : Type} : ℕ → (list a) → (list a × list a)
 | 0       xs        := ([], xs)
 | _       []        := ([], [])
 | (n + 1) (x :: xs) := let (ys, zs) := splitAt1 n xs in (x :: ys, zs)

example : splitAt1 2 [1,2,3,4] = ([1,2],[3,4]) :=
begin
  simp [splitAt1],
end

-- 2ª definición
def splitAt {a : Type} : ℕ → (list a) → (list a × list a)
 | 0 xs              := ([], xs)
 | _       []        := ([], [])
 | (n + 1) (x :: xs) := (x :: (splitAt n xs).1, (splitAt n xs).2)

example : splitAt 2 [1,2,3,4] = ([1,2],[3,4]) :=
begin
  simp [splitAt],
end

example
  (a : Type)
  (n : ℕ)
  (xs : list a)
  : (λ x, (prod.fst x) ++ (prod.snd x) = xs) (splitAt n xs) :=
begin
  induction xs with d hd IH generalizing n,
  { induction n with m hm;
    simp [splitAt] },
  { induction n with m hm,
    { simp [splitAt] },
    { simp [splitAt, IH, hm] } }
end
