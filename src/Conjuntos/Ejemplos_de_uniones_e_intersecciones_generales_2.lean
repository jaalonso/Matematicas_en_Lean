-- ---------------------------------------------------------------------
-- Ejercicio. Realizar las siguientes acciones:
-- 1. Importar la teoría data.set.lattice
-- 2. Importar la teoría data.nat.prime
-- 3. Abrir los espacios de nombre set y nat. 
-- ----------------------------------------------------------------------

import data.set.lattice   -- 1
import data.nat.prime     -- 2
open set nat              -- 3

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el conjunto de los números primos. 
-- ----------------------------------------------------------------------

def primes : set ℕ := {x | prime x}

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
begin 
  ext, 
  rw mem_bUnion_iff, 
  refl,
end

-- Prueba
-- ======

/-
⊢ (⋃ (p : ℕ) (H : p ∈ primes), {x : ℕ | p ^ 2 ∣ x}) =
    {x : ℕ | ∃ (p : ℕ) (H : p ∈ primes), p ^ 2 ∣ x}
  >> ext, 
x : ℕ
⊢ (x ∈ ⋃ (p : ℕ) (H : p ∈ primes), {x : ℕ | p ^ 2 ∣ x}) ↔
    x ∈ {x : ℕ | ∃ (p : ℕ) (H : p ∈ primes), p ^ 2 ∣ x}
  >> rw mem_bUnion_iff, 
⊢ (∃ (x_1 : ℕ) (H : x_1 ∈ primes), x ∈ {x : ℕ | x_1 ^ 2 ∣ x}) ↔
    x ∈ {x : ℕ | ∃ (p : ℕ) (H : p ∈ primes), p ^ 2 ∣ x}
  >> refl,
no goals
-/

-- Comentario: Se ha usado el lema
-- + mem_bUnion_iff : y ∈ (⋃ x ∈ s, t x) ↔ ∃ x ∈ s, y ∈ t x

-- Comprobación:
universes u v
variable α : Type u
variable β : Type v
variable s : set α
variable t : α → set β 
variable y : β
#check @mem_bUnion_iff α β s t y

example : y ∈ (⋃ x ∈ s, t x) ↔ ∃ x ∈ s, y ∈ t x :=
mem_bUnion_iff

-- 2ª demostración
-- ===============

example : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
by { ext, rw mem_bUnion_iff, refl }

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} 
-- ----------------------------------------------------------------------

example : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
by { ext, simp }

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (⋂ p ∈ primes, {x | ¬ p ∣ x}) ⊆ {x | x < 2}
-- ----------------------------------------------------------------------

example : (⋂ p ∈ primes, {x | ¬ p ∣ x}) ⊆ {x | x < 2} :=
begin
  intro x,
  contrapose!,
  simp,
  apply exists_prime_and_dvd,
end

-- Prueba
-- ======

/-
⊢ (⋂ (p : ℕ) (H : p ∈ primes), {x : ℕ | ¬p ∣ x}) ⊆ {x : ℕ | x < 2}
  >> intro x,
x : ℕ
⊢ (x ∈ ⋂ (p : ℕ) (H : p ∈ primes), {x : ℕ | ¬p ∣ x}) → x ∈ {x : ℕ | x < 2}
  >> contrapose!,
⊢ x ∉ {x : ℕ | x < 2} → (x ∉ ⋂ (p : ℕ) (H : p ∈ primes), {x : ℕ | ¬p ∣ x})
  >> simp,
⊢ 2 ≤ x → (∃ (x_1 : ℕ), x_1 ∈ primes ∧ x_1 ∣ x)
  >> apply exists_prime_and_dvd,
no goals
-/

-- Comentario: Se ha aplicado el lema
-- + exists_prime_and_dvd : 2 ≤ n → (∃ (p : ℕ), p.prime ∧ p ∣ n) 

variable n : ℕ
#check @exists_prime_and_dvd n

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (⋃ p ∈ primes, {x | x ≤ p}) = univ
-- ----------------------------------------------------------------------

example : (⋃ p ∈ primes, {x | x ≤ p}) = univ :=
begin
  apply eq_univ_of_forall,
  intro x,
  simp,
  rcases exists_infinite_primes x with ⟨p, pge, primep⟩,
  use [p, primep, pge],
end

-- Prueba
-- ======

/-
⊢ (⋃ (p : ℕ) (H : p ∈ primes), {x : ℕ | x ≤ p}) = univ
  >> apply eq_univ_of_forall,
⊢ ∀ (x : ℕ), x ∈ ⋃ (p : ℕ) (H : p ∈ primes), {x : ℕ | x ≤ p}
  >> intro x,
x : ℕ
⊢ x ∈ ⋃ (p : ℕ) (H : p ∈ primes), {x : ℕ | x ≤ p}
  >> simp,
⊢ ∃ (i : ℕ), i ∈ primes ∧ x ≤ i
  >> rcases exists_infinite_primes x with ⟨p, pge, primep⟩,
x p : ℕ,
pge : x ≤ p,
primep : p.prime
⊢ ∃ (i : ℕ), i ∈ primes ∧ x ≤ i
  >> use [p, primep, pge],
no goals
-/

-- Comentario: Se han usado los lemas
-- + eq_univ_of_forall : (∀ x, x ∈ s) → s = univ
-- + exists_infinite_primes : ∀ (n : ℕ), ∃ (p : ℕ), n ≤ p ∧ p.prime

variable α : Type*
variable s : set α
#check @eq_univ_of_forall α s
#check exists_infinite_primes
