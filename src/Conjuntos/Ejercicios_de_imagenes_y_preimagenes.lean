import data.set.function

open set function

universes u v
variable  α : Type u
variable  β : Type v
variable  f : α → β
variables s t : set α
variables u v : set β

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es inyectiva, entonces
--    f ⁻¹' (f '' s) ⊆ s 
-- ----------------------------------------------------------------------

example 
  (h : injective f) 
  : f ⁻¹' (f '' s) ⊆ s :=
begin
  intros x hx,
  have h1 : f x ∈ f '' s := hx,
  rcases h1 with ⟨y, ys, fyfx⟩,
  have h2 : y = x := h fyfx,
  rw ← h2,
  exact ys,
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
s : set α,
h : injective f
⊢ f ⁻¹' (f '' s) ⊆ s
  >> intros x hx,
x : α,
hx : x ∈ f ⁻¹' (f '' s)
⊢ x ∈ s
  >> have h1 : f x ∈ f '' s := hx,
h1 : f x ∈ f '' s
⊢ x ∈ s
  >> rcases h1 with ⟨y, ys, fyfx⟩,
y : α,
ys : y ∈ s,
fyfx : f y = f x
⊢ x ∈ s
  >> have h2 : y = x := h fyfx,
h2 : y = x
⊢ x ∈ s
  >> rw ← h2,
⊢ y ∈ s
  >> exact ys,
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f '' (f⁻¹' u) ⊆ u
-- ----------------------------------------------------------------------

example : f '' (f⁻¹' u) ⊆ u :=
begin
  rintros y ⟨x, hxu, fxy⟩,
  rw ← fxy,
  exact hxu,
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
u : set β
⊢ f '' (f ⁻¹' u) ⊆ u
  >> rintros y ⟨x, hxu, fxy⟩,
y : β,
x : α,
hxu : x ∈ f ⁻¹' u,
fxy : f x = y
⊢ y ∈ u
  >> rw ← fxy,
⊢ f x ∈ u
  >> exact hxu,
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es suprayectiva, entonces
--    u ⊆ f '' (f⁻¹' u)
-- ----------------------------------------------------------------------

example 
  (h : surjective f) 
  : u ⊆ f '' (f⁻¹' u) :=
begin
  intros y hy,
  rcases h y with ⟨x,hx⟩,
  use x,
  split,
  { simp,
    rw hx,
    exact hy},
  { exact hx },
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
u : set β,
h : surjective f
⊢ u ⊆ f '' (f ⁻¹' u)
  >> intros y hy,
y : β,
hy : y ∈ u
⊢ y ∈ f '' (f ⁻¹' u)
  >> rcases h y with ⟨x,hx⟩,
x : α,
hx : f x = y
⊢ y ∈ f '' (f ⁻¹' u)
  >> use x,
⊢ x ∈ f ⁻¹' u ∧ f x = y
  >> split,
| ⊢ x ∈ f ⁻¹' u
|   >> { simp,
| ⊢ f x ∈ u
|   >>   rw hx,
| ⊢ y ∈ u
|   >>   exact hy},
⊢ f x = y
  >> { exact hx },
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    s ⊆ t
-- entonces 
--    f '' s ⊆ f '' t
-- ----------------------------------------------------------------------

example 
  (h : s ⊆ t) 
  : f '' s ⊆ f '' t :=
begin
  rintros y ⟨x,xs,fxy⟩,
  use x,
  split,
  { apply h,
    exact xs },
  { exact fxy },
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
s t : set α,
h : s ⊆ t
⊢ f '' s ⊆ f '' t
  >> rintros y ⟨x,xs,fxy⟩,
y : β,
x : α,
xs : x ∈ s,
fxy : f x = y
⊢ y ∈ f '' t
  >> use x,
⊢ x ∈ t ∧ f x = y
  >> split,
| ⊢ x ∈ t
|   >> { apply h,
| ⊢ x ∈ s
|   >>   exact xs },
⊢ f x = y
  >> { exact fxy },
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si
--    u ⊆ v
-- entonces 
--    f ⁻¹' u ⊆ f ⁻¹' v 
-- ----------------------------------------------------------------------

example 
  (h : u ⊆ v) 
  : f ⁻¹' u ⊆ f ⁻¹' v :=
begin
  intros y hy,
  simp at *,
  apply h,
  exact hy,
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
u v : set β,
h : u ⊆ v
⊢ f ⁻¹' u ⊆ f ⁻¹' v
  >> intros y hy,
y : α,
hy : y ∈ f ⁻¹' u
⊢ y ∈ f ⁻¹' v
  >> simp at *,
hy : f y ∈ u
⊢ f y ∈ v
  >> apply h,
⊢ f y ∈ u
  >> exact hy,
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f ⁻¹' (u ∪ v) = (f ⁻¹' u) ∪ (f ⁻¹' v)
-- ----------------------------------------------------------------------

example : f ⁻¹' (u ∪ v) = (f ⁻¹' u) ∪ (f ⁻¹' v) :=
begin
  ext x,
  split,
  { intro hx,
    rcases hx with hxu | hxv,
    { left,
      apply hxu },
    { right,
      apply hxv }},
  { intro hx',
    simp,
    rcases hx' with hxu' | hxv',
    { left,
      apply hxu' },
    { right,
      apply hxv' }},
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
u v : set β
⊢ f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v
  >> ext x,
x : α
⊢ x ∈ f ⁻¹' (u ∪ v) ↔ x ∈ f ⁻¹' u ∪ f ⁻¹' v
  >> split,
| ⊢ x ∈ f ⁻¹' (u ∪ v) → x ∈ f ⁻¹' u ∪ f ⁻¹' v
|   >> { intro hx,
| hx : x ∈ f ⁻¹' (u ∪ v)
| ⊢ x ∈ f ⁻¹' u ∪ f ⁻¹' v
|   >>   rcases hx with hxu | hxv,
| | hxu : f x ∈ u
| | ⊢ x ∈ f ⁻¹' u ∪ f ⁻¹' v
| |   >>   { left,
| | ⊢ x ∈ f ⁻¹' u
| |   >>     apply hxu },
| ⊢ x ∈ f ⁻¹' u ∪ f ⁻¹' v
|   >>   { right,
| ⊢ x ∈ f ⁻¹' v
|   >>     apply hxv }},
⊢ x ∈ f ⁻¹' u ∪ f ⁻¹' v → x ∈ f ⁻¹' (u ∪ v)
  >> { intro hx',
hx' : x ∈ f ⁻¹' u ∪ f ⁻¹' v
⊢ x ∈ f ⁻¹' (u ∪ v)
  >>   simp,
⊢ f x ∈ u ∨ f x ∈ v
  >>   rcases hx' with hxu' | hxv',
| hxu' : x ∈ f ⁻¹' u
| ⊢ f x ∈ u ∨ f x ∈ v
|   >>   { left,
| ⊢ f x ∈ u
|   >>     apply hxu' },
hxv' : x ∈ f ⁻¹' v
⊢ f x ∈ u ∨ f x ∈ v
  >>   { right,
⊢ f x ∈ v
  >>     apply hxv' }},
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f '' (s ∩ t) ⊆ (f '' s) ∩ (f '' t)
-- ----------------------------------------------------------------------

example : f '' (s ∩ t) ⊆ (f '' s) ∩ (f '' t) :=
begin
  rintros y ⟨x,⟨xs,xt⟩,fxy⟩,
  split,
  { use x,
    exact ⟨xs, fxy⟩},
  { use x,
    exact ⟨xt, fxy⟩},
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
s t : set α
⊢ f '' (s ∩ t) ⊆ f '' s ∩ f '' t
  >> rintros y ⟨x,⟨xs,xt⟩,fxy⟩,
y : β,
x : α,
fxy : f x = y,
xs : x ∈ s,
xt : x ∈ t
⊢ y ∈ f '' s ∩ f '' t
  >> split,
| ⊢ y ∈ f '' s
|   >> { use x,
| ⊢ x ∈ s ∧ f x = y
|   >>   exact ⟨xs, fxy⟩},
⊢ y ∈ f '' t
  >> { use x,
⊢ x ∈ t ∧ f x = y
  >>   exact ⟨xt, fxy⟩},
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es inyectiva, entonces
--    (f '' s) ∩ (f '' t) ⊆ f '' (s ∩ t) 
-- ----------------------------------------------------------------------

example 
  (h : injective f) 
  : (f '' s) ∩ (f '' t) ⊆ f '' (s ∩ t) :=
begin
  rintros y ⟨ys,yt⟩,
  rcases ys with ⟨x,xs,fxy⟩,
  use x, 
  split,
  { split,
    { exact xs },
    { rcases yt with ⟨z,zs,fzy⟩,
      rw ←fzy at fxy,
      rw h fxy,
      exact zs }},
  { exact fxy },
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
s t : set α,
h : injective f
⊢ f '' s ∩ f '' t ⊆ f '' (s ∩ t)
  >> rintros y ⟨ys,yt⟩,
y : β,
ys : y ∈ f '' s,
yt : y ∈ f '' t
⊢ y ∈ f '' (s ∩ t)
  >> rcases ys with ⟨x,xs,fxy⟩,
x : α,
xs : x ∈ s,
fxy : f x = y
⊢ y ∈ f '' (s ∩ t)
  >> use x, 
⊢ x ∈ s ∩ t ∧ f x = y
  >> split,
| ⊢ x ∈ s ∩ t
|   >> { split,
| | ⊢ x ∈ s
| |   >>   { exact xs },
| ⊢ x ∈ t
|   >>   { rcases yt with ⟨z,zs,fzy⟩,
| z : α,
| zs : z ∈ t,
| fzy : f z = y
| ⊢ x ∈ t
|   >>     rw ←fzy at fxy,
| fxy : f x = f z
| ⊢ x ∈ t
|   >>     rw h fxy,
| fxy : f x = f z
| ⊢ z ∈ t
|   >>     exact zs }},
⊢ f x = y
  >> { exact fxy },
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (f '' s) \ (f '' t) ⊆ f '' (s \ t) 
-- ----------------------------------------------------------------------

example : (f '' s) \ (f '' t) ⊆ f '' (s \ t) :=
begin
  rintros y ⟨h1,h2⟩,
  rcases h1 with ⟨x,xs,fxy⟩,
  use x,
  split,
  { split,
    { exact xs },
    { intro h3,
      apply h2,
      use x,
      exact ⟨h3, fxy⟩}},
  { exact fxy },
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
s t : set α
⊢ f '' s \ f '' t ⊆ f '' (s \ t)
  >> rintros y ⟨h1,h2⟩,
y : β,
h1 : y ∈ f '' s,
h2 : y ∉ f '' t
⊢ y ∈ f '' (s \ t)
  >> rcases h1 with ⟨x,xs,fxy⟩,
x : α,
xs : x ∈ s,
fxy : f x = y
⊢ y ∈ f '' (s \ t)
  >> use x,
⊢ x ∈ s \ t ∧ f x = y
  >> split,
| ⊢ x ∈ s \ t
|   >> { split,
| ⊢ x ∈ s
| |   >>   { exact xs },
| ⊢ (λ (a : α), a ∉ t) x
|   >>   { intro h3,
| h3 : x ∈ t
| ⊢ false
|   >>     apply h2,
| ⊢ y ∈ f '' t
|   >>     use x,
| ⊢ x ∈ t ∧ f x = y
|   >>     exact ⟨h3, fxy⟩}},
⊢ f x = y
  >> { exact fxy },
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (f ⁻¹' u) \ (f ⁻¹' v) ⊆ f ⁻¹' (u \ v) 
-- ----------------------------------------------------------------------

example : (f ⁻¹' u) \ (f ⁻¹' v) ⊆ f ⁻¹' (u \ v) :=
begin
  rintros x ⟨hxu,hxv⟩,
  simp,
  split,
  { exact hxu },
  { intro h,
    apply hxv,
    exact h },
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
u v : set β
⊢ f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v)
  >> rintros x ⟨hxu,hxv⟩,
x : α,
hxu : x ∈ f ⁻¹' u,
hxv : x ∉ f ⁻¹' v
⊢ x ∈ f ⁻¹' (u \ v)
  >> simp,
⊢ f x ∈ u ∧ f x ∉ v
  >> split,
| ⊢ f x ∈ u
|   >> { exact hxu },
⊢ f x ∉ v
  >> { intro h,
h : f x ∈ v
⊢ false
  >>   apply hxv,
⊢ x ∈ f ⁻¹' v
  >>   exact h },
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (f '' s) ∩ v = f '' (s ∩ (f ⁻¹' v))
-- ----------------------------------------------------------------------

example : (f '' s) ∩ v = f '' (s ∩ (f ⁻¹' v)) :=
begin
  ext y,
  split,
  { rintros ⟨ys,yv⟩,
    rcases ys with ⟨x,xs,fxy⟩,
    use x,
    split,
    { split,
      { exact xs },
      { simp,
        rw fxy,
        exact yv }},
    { exact fxy }},
  { intro h,
    rcases h with ⟨x,⟨hxs,hxv⟩,fxy⟩,
    split,
    { rw ←fxy,
      exact mem_image_of_mem f hxs },
    { rw ←fxy,
      exact hxv }},
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
s : set α,
v : set β
⊢ f '' s ∩ v = f '' (s ∩ f ⁻¹' v)
  >> ext y,
y : β
⊢ y ∈ f '' s ∩ v ↔ y ∈ f '' (s ∩ f ⁻¹' v)
  >> split,
| ⊢ y ∈ f '' s ∩ v → y ∈ f '' (s ∩ f ⁻¹' v)
|   >> { rintros ⟨ys,yv⟩,
| ys : y ∈ f '' s,
| yv : y ∈ v
| ⊢ y ∈ f '' (s ∩ f ⁻¹' v)
|   >>   rcases ys with ⟨x,xs,fxy⟩,
| x : α,
| xs : x ∈ s,
| fxy : f x = y
| ⊢ y ∈ f '' (s ∩ f ⁻¹' v)
|   >>   use x,
⊢ x ∈ s ∩ f ⁻¹' v ∧ f x = y
|   >>   split,
| ⊢ x ∈ s ∩ f ⁻¹' v
|   >>   { split,
| |  ⊢ x ∈ s
| |    >>     { exact xs },
| ⊢ x ∈ f ⁻¹' v
|   >>     { simp,
| ⊢ f x ∈ v
|   >>       rw fxy,
| ⊢ y ∈ v
|   >>       exact yv }},
| ⊢ f x = y
|   >>   { exact fxy }},
⊢ y ∈ f '' (s ∩ f ⁻¹' v) → y ∈ f '' s ∩ v
  >> { intro h,
h : y ∈ f '' (s ∩ f ⁻¹' v)
⊢ y ∈ f '' s ∩ v
  >>   rcases h with ⟨x,⟨hxs,hxv⟩,fxy⟩,
x : α,
fxy : f x = y,
hxs : x ∈ s,
hxv : x ∈ f ⁻¹' v
⊢ y ∈ f '' s ∩ v
  >>   split,
| ⊢ y ∈ f '' s
|   >>   { rw ←fxy,
| ⊢ f x ∈ f '' s
|   >>     exact mem_image_of_mem f hxs },
⊢ y ∈ v
  >>   { rw ←fxy,
⊢ f x ∈ v
  >>     exact hxv }},
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f '' (s ∩ f ⁻¹' u) ⊆ (f '' s) ∪ u
-- ----------------------------------------------------------------------

example : f '' (s ∩ f ⁻¹' u) ⊆ (f '' s) ∪ u :=
begin
  intros y h,
  rcases h with ⟨x,⟨xs,xu⟩,fxy⟩,
  right,
  rw ←fxy,
  exact xu,
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
s : set α,
u : set β
⊢ f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u
  >> intros y h,
y : β,
h : y ∈ f '' (s ∩ f ⁻¹' u)
⊢ y ∈ f '' s ∪ u
  >> rcases h with ⟨x,⟨xs,xu⟩,fxy⟩,
x : α,
fxy : f x = y,
xs : x ∈ s,
xu : x ∈ f ⁻¹' u
⊢ y ∈ f '' s ∪ u
  >> right,
⊢ y ∈ u
  >> rw ←fxy,
⊢ f x ∈ u
  >> exact xu,
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    s ∩ f ⁻¹' u ⊆ f ⁻¹' ((f '' s) ∩ u) :=
-- ----------------------------------------------------------------------

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' ((f '' s) ∩ u) :=
begin
  rintros x ⟨xs,xu⟩,
  simp at xu,
  split,
  { exact mem_image_of_mem f xs },
  { exact xu },
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
s : set α,
u : set β
⊢ s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u)
  >> rintros x ⟨xs,xu⟩,
x : α,
xs : x ∈ s,
xu : x ∈ f ⁻¹' u
⊢ x ∈ f ⁻¹' (f '' s ∩ u)
  >> simp at xu,
xu : f x ∈ u
⊢ x ∈ f ⁻¹' (f '' s ∩ u)
  >> split,
| ⊢ f x ∈ f '' s
|   >> { exact mem_image_of_mem f xs },
⊢ f x ∈ u
  >> { exact xu },
no goals
-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    s ∪ f ⁻¹' u ⊆ f ⁻¹' ((f '' s) ∪ u)
-- ----------------------------------------------------------------------

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' ((f '' s) ∪ u) :=
begin
  rintros x (xs | xu),
  { left,
    exact mem_image_of_mem f xs },
  { right,
    exact xu },
end

-- Prueba
-- ======

/-
α : Type u,
β : Type v,
f : α → β,
s : set α,
u : set β
⊢ s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u)
  >> rintros x (xs | xu),
| x : α,
| xs : x ∈ s
| ⊢ x ∈ f ⁻¹' (f '' s ∪ u)
|   >> { left,
| ⊢ f x ∈ f '' s
|   >>   exact mem_image_of_mem f xs },
xu : x ∈ f ⁻¹' u
⊢ x ∈ f ⁻¹' (f '' s ∪ u)
  >> { right,
⊢ f x ∈ u
  >>   exact xu },
no goals
-/

