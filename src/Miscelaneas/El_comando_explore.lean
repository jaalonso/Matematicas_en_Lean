import tactic

-- #explode and_iff_left

-- Colocando el cursor sobre explode se obtiene
--    and_iff_left : ∀ {a b : Prop}, b → (a ∧ b ↔ a)
--    0 │   │ a         ├ Prop
--    1 │   │ b         ├ Prop
--    2 │   │ hb        ├ b
--    3 │   │ and.left  │ a ∧ b → a
--    4 │   │ ha        │ ┌ a
--    5 │4,2│ and.intro │ │ a ∧ b
--    6 │4,5│ ∀I        │ a → a ∧ b
--    7 │3,6│ iff.intro │ a ∧ b ↔ a
--    8 │2,7│ ∀I        │ b → (a ∧ b ↔ a)
--    9 │1,8│ ∀I        │ ∀ {b : Prop}, b → (a ∧ b ↔ a)
--    10│0,9│ ∀I        │ ∀ {a b : Prop}, b → (a ∧ b ↔ a)

variables (R : Type) [add_group R]

-- #explode neg_eq_of_add_eq_zero

-- Colocando el cursor sobre explode se obtiene
--    neg_eq_of_add_eq_zero : ∀ {G : Type u} [_inst_1 : add_group G] {a b : G}, a + b = 0 → -a = b
--    0 │    │ G                     ├ Type u
--    1 │    │ _inst_1               ├ add_group G
--    2 │    │ a                     ├ G
--    3 │    │ b                     ├ G
--    4 │    │ h                     ├ a + b = 0
--    5 │    │ neg_add_self          │ -a + a = 0
--    6 │5,4 │ left_neg_eq_right_neg │ -a = b
--    7 │4,6 │ ∀I                    │ a + b = 0 → -a = b
--    8 │3,7 │ ∀I                    │ ∀ {b : G}, a + b = 0 → -a = b
--    9 │2,8 │ ∀I                    │ ∀ {a b : G}, a + b = 0 → -a = b
--    10│1,9 │ ∀I                    │ ∀ [_inst_1 : add_group G] {a b : G}, a + b = 0 → -a = b
--    11│0,10│ ∀I                    │ ∀ {G : Type u} [_inst_1 : add_group G] {a b : G}, a + b = 0 → -a = b

theorem neg_eq_of_add_eq_zero'
  {a b : R}
  (h : a + b = 0)
  : -a = b :=
begin
  rw ← add_right_neg a at h,
  rw add_left_cancel h
end

-- #explode neg_eq_of_add_eq_zero'

-- Colocando el cursor sobre explode se obtiene
--    neg_eq_of_add_eq_zero' : ∀ (R : Type) [_inst_1 : add_group R] {a b : R}, a + b = 0 → -a = b
--    0 │     │ R               ├ Type
--    1 │     │ _inst_1         ├ add_group R
--    2 │     │ a               ├ R
--    3 │     │ b               ├ R
--    4 │     │ h               ├ a + b = 0
--    5 │     │ eq.refl         │ -a = b = (-a = b)
--    6 │     │ eq.refl         │ a + b = 0 = (a + b = 0)
--    7 │     │ add_right_neg   │ a + -a = 0
--    8 │7    │ eq.symm         │ 0 = a + -a
--    9 │6,8  │ eq.rec          │ (λ (_a : R), a + b = 0 = (a + b = _a)) (a + -a)
--    10│9,4  │ eq.mp           │ a + b = a + -a
--    11│10   │ add_left_cancel │ b = -a
--    12│5,11 │ eq.rec          │ (λ (_a : R), -a = b = (-a = _a)) (-a)
--    13│12   │ id              │ -a = b = (-a = -a)
--    14│     │ eq.refl         │ -a = -a
--    15│13,14│ eq.mpr          │ -a = b
--    16│4,15 │ ∀I              │ a + b = 0 → -a = b
--    17│3,16 │ ∀I              │ ∀ {b : R}, a + b = 0 → -a = b
--    18│2,17 │ ∀I              │ ∀ {a b : R}, a + b = 0 → -a = b
--    19│1,18 │ ∀I              │ ∀ [_inst_1 : add_group R] {a b : R}, a + b = 0 → -a = b
--    20│0,19 │ ∀I              │ ∀ (R : Type) [_inst_1 : add_group R] {a b : R}, a + b = 0 → -a = b
