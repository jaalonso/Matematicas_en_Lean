-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si 0 < 0, entonces a > 37 para cualquier
-- número a. 
-- ----------------------------------------------------------------------

variable a : ℕ

-- 1ª demostración
-- ===============

example 
  (h : 0 < 0) 
  : a > 37 :=
begin
  exfalso,
  apply lt_irrefl 0 h,
end

-- Prueba
-- ======

/-
a : ℕ,
h : 0 < 0
⊢ a > 37
  >> exfalso,
a : ℕ,
h : 0 < 0
⊢ false
  >> apply lt_irrefl 0 h,
no goals
-/

-- Comentario: La táctica exfalso sustituye el objetivo por false.

-- 2ª demostración
-- ===============

example 
  (h : 0 < 0) 
  : a > 37 :=
absurd h (lt_irrefl 0)

-- 3ª demostración
-- ===============

example 
  (h : 0 < 0) 
  : a > 37 :=
begin
  have h' : ¬ 0 < 0,
    from lt_irrefl 0,
  contradiction,
end

-- Prueba
-- ======

/-
a : ℕ,
h : 0 < 0
⊢ a > 37
  >> have h' : ¬ 0 < 0,
  >>   from lt_irrefl 0,
h' : ¬0 < 0
⊢ a > 37
  >> contradiction,
no goals
-/

-- Comentario: La táctica contradiction busca dos hipótesis
-- contradictorias. 
