-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la librería de los números reales.
-- 2. Declarar x, y, a y b como variables sobre los reales.
-- 3. Crear el espacio de nombres my_abs.
-- ----------------------------------------------------------------------

import data.real.basic    -- 1
variables {x y a b : ℝ}   -- 2
namespace my_abs          -- 3

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    x ≤ abs x
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : x ≤ abs x :=
begin
  cases (le_or_gt 0 x) with h1 h2,
  { rw abs_of_nonneg h1 },
  { rw abs_of_neg h2,
    apply left.self_le_neg,
    apply le_of_lt h2 },
end

-- Prueba
-- ======

/-
x : ℝ
⊢ x ≤ abs x
  >> cases (le_or_gt 0 x) with h1 h2,
| h1 : 0 ≤ x
| ⊢ x ≤ abs x
  >> { rw abs_of_nonneg h1 },
h2 : 0 > x
⊢ x ≤ abs x
  >> { rw abs_of_neg h2,
⊢ x ≤ -x
  >>   apply self_le_neg,
⊢ x ≤ 0
  >>   apply le_of_lt h2 },
no goals
-/

-- Comentario: Se han usado los siguientes lemas
-- + le_or_gt x y : x ≤ y ∨ x > y
-- + abs_of_nonneg : 0 ≤ x → abs x = x
-- + abs_of_neg : x < 0 → abs x = -x
-- + self_le_neg : x ≤ 0 → x ≤ -x
-- + le_of_lt : x < y → x ≤ y

-- Comprobación
-- #check (@le_or_gt ℝ _ x y)
-- #check (@abs_of_nonneg ℝ _ x)
-- #check (@abs_of_neg ℝ _ x)
-- #check (@self_le_neg ℝ _ x)
-- #check (@le_of_lt ℝ _ x y)

-- 2ª demostración
-- ===============

example : x ≤ abs x :=
begin
  unfold abs,
  exact le_max_left x (-x),
end

-- Comentarios:
-- 1. La táctica (unfold e) despliega la definición de e.
-- 2. La definición de abs
--    + abs (a : α) : α := max a (-a)
-- 3. Se ha usado el lema
--    + le_max_left x y : x ≤ max x y

-- Comprobación
-- #check (@le_max_left ℝ _ x y)
-- #print abs

-- 3ª demostración
-- ===============

example : x ≤ abs x :=
le_max_left x (-x)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--    -x ≤ abs x
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

theorem neg_le_abs_self : -x ≤ abs x :=
begin
  cases (le_or_gt 0 x) with h1 h2,
  { rw abs_of_nonneg h1,
    apply neg_le_self h1 },
  { rw abs_of_neg h2 },
end

-- Prueba
-- ======

/-
x : ℝ
⊢ -x ≤ abs x
  >> cases (le_or_gt 0 x) with h1 h2,
| h1 : 0 ≤ x
| ⊢ -x ≤ abs x
|   >> { rw abs_of_nonneg h1,
| ⊢ -x ≤ x
|   >>   apply neg_le_self h1 },
h2 : 0 > x
⊢ -x ≤ abs x
  >> { rw abs_of_neg h2 },
no goals
-/

-- Comentario: Los lemas utilizados son
-- + le_or_gt x y : x ≤ y ∨ x > y
-- + abs_of_nonneg : 0 ≤ x → abs x = x
-- + neg_le_self : 0 ≤ x → -x ≤ x
-- + abs_of_neg : x < 0 → abs x = -x

-- Comprobación
-- #check (@le_or_gt ℝ _ x y)
-- #check (@abs_of_nonneg ℝ _ x)
-- #check (@neg_le_self ℝ _ x)
-- #check (@abs_of_neg ℝ _ x)

-- 2ª demostración
-- ===============

example : -x ≤ abs x :=
begin
  unfold abs,
  exact le_max_right x (-x),
end

-- Comentarios:
-- 1. La táctica (unfold e) despliega la definición de e.
-- 2. La definición de abs
--    + abs (a : α) : α := max a (-a)
-- 3. Se ha usado el lema
--    + le_max_right x y : y ≤ max x y

-- Comprobación:
-- #check (@le_max_right ℝ _ x y)

-- 3ª demostración
-- ===============

example : -x ≤ abs x :=
le_max_right x (-x)

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que si
--    0 ≤ a + b
--    0 ≤ a
-- entonces
--    abs (a + b) ≤ abs a + abs b
-- ----------------------------------------------------------------------

open_locale classical

lemma aux1
  (h1 : 0 ≤ a + b)
  (h2 : 0 ≤ a)
  : abs (a + b) ≤ abs a + abs b :=
begin
  by_cases h3 : 0 ≤ b,
  show abs (a + b) ≤ abs a + abs b,
    calc
      abs (a + b) ≤ abs (a + b)   : by apply le_refl
              ... = a + b         : by rw (abs_of_nonneg h1)
              ... = abs a + b     : by rw (abs_of_nonneg h2)
              ... = abs a + abs b : by rw (abs_of_nonneg h3),
  have h4 : b ≤ 0,
    from le_of_lt (lt_of_not_ge h3),
  show abs (a + b) ≤ abs a + abs b,
    calc
      abs (a + b) = a + b         : by rw (abs_of_nonneg h1)
              ... = abs a + b     : by rw (abs_of_nonneg h2)
              ... ≤ abs a + 0     : add_le_add_left h4 _
              ... ≤ abs a + -b    : add_le_add_left (neg_nonneg_of_nonpos h4) _
              ... = abs a + abs b : by rw (abs_of_nonpos h4),
end

-- Prueba
-- ======

/-
a b : ℝ,
h1 : 0 ≤ a + b,
h2 : 0 ≤ a
⊢ abs (a + b) ≤ abs a + abs b
  >> by_cases h3 : 0 ≤ b,
| h3 : 0 ≤ b
| ⊢ abs (a + b) ≤ abs a + abs b
|   >> show abs (a + b) ≤ abs a + abs b, calc
|   >>   abs (a + b) ≤ abs (a + b)   : by apply le_refl
|   >>           ... = a + b         : by rw (abs_of_nonneg h1)
|   >>           ... = abs a + b     : by rw (abs_of_nonneg h2)
|   >>           ... = abs a + abs b : by rw (abs_of_nonneg h3),
h3 : ¬0 ≤ b
⊢ abs (a + b) ≤ abs a + abs b
  >> have h4 : b ≤ 0,
  >>   from le_of_lt (lt_of_not_ge h3),
h4 : b ≤ 0
⊢ abs (a + b) ≤ abs a + abs b
  >> show abs (a + b) ≤ abs a + abs b, calc
  >>   abs (a + b) = a + b         : by rw (abs_of_nonneg h1)
  >>           ... = abs a + b     : by rw (abs_of_nonneg h2)
  >>           ... ≤ abs a + 0     : add_le_add_left h4 _
  >>           ... ≤ abs a + -b    : add_le_add_left (neg_nonneg_of_nonpos h4)
  >>           ... = abs a + abs b : by rw (abs_of_nonpos h4),
-/

-- Comentarios:
-- 1. La táctica (by_cases h : p) aplica el principio de tercio excluso
--    sobre p; es decir, considera dos casos: en el primero le añade la
--    hipótesis (h : p) y en el segundo, (h : ¬p).
-- 2. Para aplicar la táctica by_cases hay que habilitar la lógica
--    clásica.
-- 3. Se han usado los siguientes lemas
--    + le_refl x : x ≤ x
--    + abs_of_nonneg : 0 ≤ x → abs x = x
--    + le_of_lt : x < y → x ≤ y
--    + lt_of_not_ge : ¬x ≥ y → x < y
--    + add_le_add_left : x ≤ y → ∀ (c : ℝ), c + x ≤ c + y
--    + neg_nonneg_of_nonpos : x ≤ 0 → 0 ≤ -x
--    + abs_of_nonpos : x ≤ 0 → abs x = -x

-- Comprobación:
-- #check (@le_refl ℝ _ x)
-- #check (@abs_of_nonneg ℝ _ x)
-- #check (@le_of_lt ℝ _ x y)
-- #check (@lt_of_not_ge ℝ _ x y)
-- #check (@add_le_add_left ℝ _ x y)
-- #check (@neg_nonneg_of_nonpos ℝ _ x)
-- #check (@abs_of_nonpos ℝ _ x)

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que si
--    0 ≤ a + b
-- entonces
--    abs (a + b) ≤ abs a + abs b
-- ----------------------------------------------------------------------

lemma aux2
  (h1 : 0 ≤ a + b)
  : abs (a + b) ≤ abs a + abs b :=
begin
  by_cases h2 : 0 ≤ a,
    exact @aux1 a b h1 h2,
  rw add_comm at h1,
  have h3 : 0 ≤ b,
    linarith,
  rw add_comm,
  rw add_comm (abs a),
  exact @aux1 b a h1 h3,
end

-- ---------------------------------------------------------------------
-- Ejercicio 6. Demostrar que
--    abs (x + y) ≤ abs x + abs y
-- ----------------------------------------------------------------------

theorem abs_add : abs (x + y) ≤ abs x + abs y :=
begin
  by_cases h2 : 0 ≤ x + y,
    { exact @aux2 x y h2 },
  have h3 : x + y ≤ 0,
    by exact le_of_not_ge h2,
  have h4: -x + -y = -(x + y),
    by rw neg_add,
  have h5 : 0 ≤ -(x + y),
    from neg_nonneg_of_nonpos h3,
  have h6 : 0 ≤ -x + -y,
    { rw [← h4] at h5,
      exact h5 },
  calc
     abs (x + y) = abs (-x + -y)       : by rw [← abs_neg, neg_add]
             ... ≤ abs (-x) + abs (-y) : aux2 h6
             ... = abs x + abs y       : by rw [abs_neg, abs_neg],
end

-- Prueba
-- ======

/-
x y : ℝ
⊢ abs (x + y) ≤ abs x + abs y
  >> by_cases h2 : 0 ≤ x + y,
| h2 : 0 ≤ x + y
| ⊢ abs (x + y) ≤ abs x + abs y
|   >>   { exact @aux2 x y h2 },
h2 : ¬0 ≤ x + y
⊢ abs (x + y) ≤ abs x + abs y
  >> have h3 : x + y ≤ 0,
  >>   by exact le_of_not_ge h2,
x y : ℝ,
h2 : ¬0 ≤ x + y,
h3 : x + y ≤ 0
⊢ abs (x + y) ≤ abs x + abs y
  >> have h4: -x + -y = -(x + y),
  >>   by rw neg_add,
x y : ℝ,
h2 : ¬0 ≤ x + y,
h3 : x + y ≤ 0,
h4 : -x + -y = -(x + y)
⊢ abs (x + y) ≤ abs x + abs y
  >> have h5 : 0 ≤ -(x + y),
  >>   from neg_nonneg_of_nonpos h3,
x y : ℝ,
h2 : ¬0 ≤ x + y,
h3 : x + y ≤ 0,
h4 : -x + -y = -(x + y),
h5 : 0 ≤ -(x + y)
⊢ abs (x + y) ≤ abs x + abs y
  >> have h6 : 0 ≤ -x + -y,
  >>   { rw [← h4] at h5,
x y : ℝ,
h2 : ¬0 ≤ x + y,
h3 : x + y ≤ 0,
h4 : -x + -y = -(x + y),
h5 : 0 ≤ -x + -y
⊢ 0 ≤ -x + -y
  >>     exact h5 },
x y : ℝ,
h2 : ¬0 ≤ x + y,
h3 : x + y ≤ 0,
h4 : -x + -y = -(x + y),
h5 : 0 ≤ -(x + y),
h6 : 0 ≤ -x + -y
⊢ abs (x + y) ≤ abs x + abs y
  >> calc
  >>    abs (x + y) = abs (-x + -y)       : by rw [← abs_neg, neg_add]
  >>            ... ≤ abs (-x) + abs (-y) : aux2 h6
  >>            ... = abs x + abs y       : by rw [abs_neg, abs_neg],
-/

-- Comentario: Se han usado los lemas
-- + le_of_not_ge : ¬x ≥ y → x ≤ y
-- + neg_add x y : -(x + y) = -x + -y
-- + neg_nonneg_of_nonpos : x ≤ 0 → 0 ≤ -x

-- Comprobación:
-- #check (@le_of_not_ge ℝ _ x y)
-- #check (@neg_add ℝ _ x y)
-- #check (@neg_nonneg_of_nonpos ℝ _ x)

end my_abs
