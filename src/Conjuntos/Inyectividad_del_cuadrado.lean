import data.real.basic
import data.real.sqrt

open set real

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la función cuadrado es inyectiva sobre los
-- números no negativos.
-- ----------------------------------------------------------------------

example : inj_on sqrt { x | x ≥ 0 } :=
begin
  intros x hx y hy,
  intro e,
  calc
    x   = (sqrt x)^2 : by rw sqr_sqrt hx
    ... = (sqrt y)^2 : by rw e
    ... = y          : by rw sqr_sqrt hy,
end

-- Prueba
-- ======

/-
⊢ inj_on sqrt {x : ℝ | x ≥ 0}
  >> intros x y xnonneg ynonneg,
⊢ inj_on sqrt {x : ℝ | x ≥ 0}
  >> intro e,
e : x.sqrt = y.sqrt
⊢ x = y
  >> calc
  >>   x   = (sqrt x)^2 : by rw sqr_sqrt xnonneg
  >>   ... = (sqrt y)^2 : by rw e
  >>   ... = y          : by rw sqr_sqrt ynonneg,
no goals
-/

-- Comentario: Se ha usado el lema
-- + sqr_sqrt : 0 ≤ x → (sqrt x) ^ 2 = x

-- Comprobación:
variable (x : ℝ)
-- #check @sqr_sqrt x

example : inj_on (λ (x : ℝ), x^2) { x | x ≥ 0 } :=
begin
  intros x xnonneg y ynonneg,
  simp,
  intro e,
  calc
    x   = sqrt (x ^ 2) : by rw sqrt_sqr xnonneg
    ... = sqrt (y ^ 2) : by rw e
    ... = y            : by rw sqrt_sqr ynonneg,
end

-- Prueba
-- ======

/-
⊢ inj_on (λ (x : ℝ), x ^ 2) {x : ℝ | x ≥ 0}
  >> intros x y xnonneg ynonneg,
x y : ℝ,
xnonneg : x ∈ {x : ℝ | x ≥ 0},
ynonneg : y ∈ {x : ℝ | x ≥ 0}
⊢ (λ (x : ℝ), x ^ 2) x = (λ (x : ℝ), x ^ 2) y → x = y
  >> simp,
⊢ x ^ 2 = y ^ 2 → x = y
  >> intro e,
e : x ^ 2 = y ^ 2
⊢ x = y
  >> calc
  >>   x   = sqrt (x ^ 2) : by rw sqrt_sqr xnonneg
  >>   ... = sqrt (y ^ 2) : by rw e
  >>   ... = y            : by rw sqrt_sqr ynonneg,
no goals
-/

-- Comentario: Se ha usado el lema
-- + sqrt_sqr : 0 ≤ x → (x ^ 2).sqrt = x

-- #check @sqrt_sqr x
