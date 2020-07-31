-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones:
-- 1. Importar la librería data.nat.prime data.nat.parity
-- 2. Abrir el espacio de nombres nat.
-- 3. Declarar s como variable sobre conjuntos de números naturales.
-- ----------------------------------------------------------------------

import data.nat.prime data.nat.parity   -- 1
open nat                                -- 2
variable (s : set ℕ)                    -- 3

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si los elementos de s no son pares y si los
-- elementos de s son primos, entonces los elementos de s no son pares
-- pero sí son primpos.
-- ----------------------------------------------------------------------

example 
  (h₀ : ∀ x ∈ s, ¬ even x) 
  (h₁ : ∀ x ∈ s, prime x) 
  : ∀ x ∈ s, ¬ even x ∧ prime x :=
begin
  intros x xs,
  split,
  { apply h₀ x xs },
  { apply h₁ x xs },
end

-- Prueba
-- ======

/-
s : set ℕ,
h₀ : ∀ (x : ℕ), x ∈ s → ¬x.even,
h₁ : ∀ (x : ℕ), x ∈ s → x.prime
⊢ ∀ (x : ℕ), x ∈ s → ¬x.even ∧ x.prime
  >> intros x xs,
x : ℕ,
xs : x ∈ s
⊢ ¬x.even ∧ x.prime
  >> split,
| ⊢ ¬x.even
|   >> { apply h₀ x xs },
⊢ x.prime
  >> { apply h₁ x xs },
no goals
-/

-- Comentario: La táctica (intros x xs) si la conclusión es (∀ y ∈ s, P y) 
-- y una hipótesis es (s : set α), entonces añade las hipótesis (x : α)
-- y (xs : x ∈ s) y cambia la conclusión a (P x). 

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si s tiene algún elemento primo impar,
-- entonces tiene algún elemento primo.
-- ----------------------------------------------------------------------

example 
  (h : ∃ x ∈ s, ¬ even x ∧ prime x) 
  : ∃ x ∈ s, prime x :=
begin
  rcases h with ⟨x, xs, _, prime_x⟩,
  use [x, xs, prime_x],
end

-- Prueba
-- ======

/-
s : set ℕ,
h : ∃ (x : ℕ) (H : x ∈ s), ¬x.even ∧ x.prime
⊢ ∃ (x : ℕ) (H : x ∈ s), x.prime
  >> rcases h with ⟨x, xs, _, prime_x⟩,
xs : x ∈ s,
h_h_h_left : ¬x.even,
prime_x : x.prime
⊢ ∃ (x : ℕ) (H : x ∈ s), x.prime
  >> use [x, xs, prime_x],
no goals
-/

-- Comentarios: 
-- 1. La táctica (cases h with ⟨x, xs, h1, h2⟩) si la
--    hipótesis es (∃ y ∈ s, P y ∧ Q y) y una hipótesis es (s : set α),
--    entonces quita h y añade las hipótesis (x : s), (h1 : P x) y
--    (h2 : Q x).
-- 2. La táctica (use [x, xs, h]) resuelve la conclusión 
--    (∃ x ∈ s, P x) si xs es una prueba de (x ∈ s) y h lo es de (P x). 
 
