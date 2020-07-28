-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar el límite del producto de dos sucesiones
-- convergentes es el producto de sus límites.
-- ----------------------------------------------------------------------

import .Definicion_de_convergencia
import .Convergencia_de_la_funcion_constante
import .Convergencia_de_la_suma
import .Convergencia_del_producto_por_una_constante
import .Acotacion_de_convergentes
import .Producto_por_sucesion_convergente_a_cero
import tactic

variables {s t : ℕ → ℝ} {a b : ℝ}

theorem converges_to_mul
  (cs : converges_to s a) 
  (ct : converges_to t b)
  : converges_to (λ n, s n * t n) (a * b) :=
begin
  have h₁ : converges_to (λ n, s n * (t n - b)) 0,
  { apply aux cs,
    convert converges_to_add ct (converges_to_const (-b)),
    ring },
  convert (converges_to_add h₁ (@converges_to_mul_const s a b cs)),
  { ext, 
    ring },
  { ring },
end

-- Prueba
-- ======

/-
s t : ℕ → ℝ,
a b : ℝ,
cs : converges_to s a,
ct : converges_to t b
⊢ converges_to (λ (n : ℕ), s n * t n) (a * b)
  >> have h₁ : converges_to (λ n, s n * (t n - b)) 0,
| ⊢ converges_to (λ (n : ℕ), s n * (t n - b)) 0
|   >> { apply aux cs,
| ⊢ converges_to (λ (n : ℕ), t n - b) 0
|   >>   convert converges_to_add ct (converges_to_const (-b)),
| ⊢ 0 = b + -b
|   >>   ring },
h₁ : converges_to (λ (n : ℕ), s n * (t n - b)) 0
⊢ converges_to (λ (n : ℕ), s n * t n) (a * b)
  >> convert (converges_to_add h₁ (@converges_to_mul_const s a b cs)),
| ⊢ (λ (n : ℕ), s n * t n) = λ (n : ℕ), s n * (t n - b) + b * s n
|   >> { ext,
| x : ℕ
| ⊢ s x * t x = s x * (t x - b) + b * s x 
|   >>   ring },
⊢ a * b = 0 + b * a
  >> { ring },
no goals
-/

