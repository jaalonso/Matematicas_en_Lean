-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    [a,b] - (a,b) = {a,b}
-- ----------------------------------------------------------------------

import data.set.intervals.basic

open set

variables {α : Type*}  [linear_order α]
variables {a b : α}

open_locale classical

-- 1ª demostración
-- ===============

lemma aux 
  (h : a < b)  
  (x : α) 
  : (x ∈ Icc a b \ Ioo a b) ↔ x ∈ ({a, b} : set α) :=
begin
  by_cases h' : a < x,
  { simp [h', ne_of_gt h'],
    split;
    simp [le_antisymm_iff, le_of_lt h'] 
      {contextual := tt} },
  { push_neg at h',
    simp [h', ne_of_lt (lt_of_le_of_lt h' h), le_trans h' (le_of_lt h)],
    simp [le_antisymm_iff, h'] },
end

example     
  (h : a < b)   
  : Icc a b \ Ioo a b = {a, b} :=
ext (aux h)

-- 2ª demostración
-- ===============

example 
  (h : a < b)
  : Icc a b \ Ioo a b = {a, b} :=
Icc_diff_Ioo_same $ le_of_lt h


