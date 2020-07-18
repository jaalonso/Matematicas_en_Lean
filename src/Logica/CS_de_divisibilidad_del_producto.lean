-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si m divide a n o a k, entonces divide a 
-- m * k.
-- ----------------------------------------------------------------------

import tactic

variables {m n k : ℕ} 

-- 1ª demostración
-- ===============

example 
  (h : m ∣ n ∨ m ∣ k) 
  : m ∣ n * k :=
begin
  rcases h with h1 | h2,
  { exact dvd_mul_of_dvd_left h1 k },
  { exact dvd_mul_of_dvd_right h2 n },
end

-- Prueba
-- ======

/-
m n k : ℕ,
h : m ∣ n ∨ m ∣ k
⊢ m ∣ n * k
  >> rcases h with h1 | h2,
| h1 : m ∣ n
| ⊢ m ∣ n * k
|   >> { exact dvd_mul_of_dvd_left h1 k },
h2 : m ∣ k
⊢ m ∣ n * k
  >> { exact dvd_mul_of_dvd_right h2 n },
no goals
-/

-- Comentario: Se han usado los lemas
-- + dvd_mul_of_dvd_left : m ∣ n → ∀ (c : ℕ), m ∣ n * c
-- + dvd_mul_of_dvd_right : m ∣ n → ∀ (c : ℕ), m ∣ c * n 

-- Comprobación
#check (@dvd_mul_of_dvd_left ℕ _ m n)
#check (@dvd_mul_of_dvd_right ℕ _ m n)

-- 2ª demostración
-- ===============

example 
  {m n k : ℕ} 
  (h : m ∣ n ∨ m ∣ k) 
  : m ∣ n * k :=
begin
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩,
  { rw [mul_assoc],
    apply dvd_mul_right },
  rw [mul_comm, mul_assoc],
  apply dvd_mul_right,
end

-- Prueba
-- ======

/-
m n k : ℕ,
h : m ∣ n ∨ m ∣ k
⊢ m ∣ n * k
  >> rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩,
| m k a : ℕ
| ⊢ m ∣ m * a * k
|   >> { rw [mul_assoc],
| ⊢ m ∣ m * (a * k)
|   >>   apply dvd_mul_right },
m n b : ℕ
⊢ m ∣ n * (m * b)
  >> rw [mul_comm, mul_assoc],
⊢ m ∣ m * (b * n)
  >> apply dvd_mul_right
no goals
-/

-- Comentario: Se han usado los siguientes lemas:
-- + mul_assoc m n k : m * n * k = m * (n * k) 
-- + dvd_mul_right m n : m ∣ m * n 
-- + mul_comm m n : m * n = n * m 

-- Comprobación
#check (@mul_assoc ℕ _ m n k)
#check (@dvd_mul_right ℕ _ m n)
#check (@mul_comm ℕ _ m n)
