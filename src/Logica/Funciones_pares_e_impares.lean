-- ---------------------------------------------------------------------
-- Ejercicio 1. Realizar las siguientes acciones:
-- 1. Importar la teoría de los números reales.
-- 2. Declarar f y g como variables sobre funciones de ℝ en ℝ.
-- ----------------------------------------------------------------------

import data.real.basic                                               -- 1

namespace oculto

variables (f g : ℝ → ℝ)                                              -- 2

-- ---------------------------------------------------------------------
-- Ejercicio 2. Definir la función
--    even (ℝ → ℝ) → Prop
-- tal que (even f) afirma que f es par.
-- ----------------------------------------------------------------------

def even (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)

-- ---------------------------------------------------------------------
-- Ejercicio 3. Definir la función
--    odd (ℝ → ℝ) → Prop
-- tal que (odd f) afirma que f es impar.
-- ----------------------------------------------------------------------

def odd  (f : ℝ → ℝ) : Prop := ∀ x, f x = - f (-x)

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que la suma de dos funciones pares es par.
-- ----------------------------------------------------------------------

example
  (ef : even f)
  (eg : even g)
  : even (λ x, f x + g x) :=
begin
  intro x,
  calc
    (λ x, f x + g x) x = f x + g x       : rfl
                   ... = f (-x) + g (-x) : by rw [ef, eg]
end

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que la suma de dos funciones impares es par.
-- ----------------------------------------------------------------------

example
  (of : odd f)
  (og : odd g)
  : even (λ x, f x * g x) :=
begin
  intro x,
  calc
    (λ x, f x * g x) x
        = f x * g x               : rfl
    ... = -f (-x) * -g (-x)       : by rw [of, og]
    ... = f (-x) * g (-x)         : by rw neg_mul_neg
    ... = ((λ x, f x * g x) (-x)) : rfl
end

-- ---------------------------------------------------------------------
-- Ejercicio 6. Demostrar que el producto de una función par por una
-- impar es impar.
-- ----------------------------------------------------------------------

example
  (ef : even f)
  (og : odd g)
  : odd (λ x, f x * g x) :=
begin
  intro x,
  calc
    (λ x, f x * g x) x
        = f x * g x                : rfl
    ... = f (-x) * -g (-x)         : by rw [ef, og]
    ... = -(f (-x) * g (-x))       : by rw neg_mul_eq_mul_neg
    ... = -((λ x, f x * g x) (-x)) : rfl
end

-- ---------------------------------------------------------------------
-- Ejercicio 7. Demostrar que si f es par y g es impar, entonces f ∘ g
-- es par.
-- ----------------------------------------------------------------------

example
  (ef : even f)
  (og : odd g)
  : even (λ x, f (g x)) :=
begin
  intro x,
  calc
    (λ x, f (g x)) x
        = f (g x)               : rfl
    ... = f (-g (-x))           : by rw og
    ... = f (g (-x))            : by rw ← ef
    ... = ((λ x, f (g x)) (-x)) : rfl
end

end oculto
