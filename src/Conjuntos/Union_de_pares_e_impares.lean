-- ---------------------------------------------------------------------
-- Ejercicio. Ejercutar las siguientes acciones
-- 1. Importar la librería data.set.basic data.nat.parity
-- 2. Abrir los espacios de nombres set y nat.
-- ----------------------------------------------------------------------

import data.set.basic data.nat.parity

open set nat

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el conjunto de los números pares. 
-- ----------------------------------------------------------------------

def evens : set ℕ := {n | even n}

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el conjunto de los números impares. 
-- ----------------------------------------------------------------------

def odds :  set ℕ := {n | ¬ even n}

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar la unión de los pares e impares es el universal.
-- ----------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : evens ∪ odds = univ :=
begin
  rw [evens, odds],
  ext n,
  simp,
  apply classical.em,
end

-- Prueba
-- ======

/-
⊢ evens ∪ odds = univ
  >> rw [evens, odds],
⊢ {n : ℕ | n.even} ∪ {n : ℕ | ¬n.even} = univ
  >> ext n,
n : ℕ
⊢ n ∈ {n : ℕ | n.even} ∪ {n : ℕ | ¬n.even} ↔ n ∈ univ
  >> simp,
⊢ n.even ∨ ¬n.even
  >> apply classical.em,
no goals
-/

-- 2ª demostración
-- ===============

example : evens ∪ odds = univ :=
begin
  ext n,
  simp,
  apply classical.em,
end

-- Prueba
-- ======

/-
⊢ evens ∪ odds = univ
  >> ext n,
n : ℕ
⊢ n ∈ evens ∪ odds ↔ n ∈ univ
  >> simp,
⊢ n ∈ evens ∨ n ∈ odds
  >> apply classical.em,
no goals
-/

