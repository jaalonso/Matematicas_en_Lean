import data.set.basic tactic

open set 

-- 1ª demostración
example
  {α : Type*} 
  {U V S A B : set α} 
  : (U ∩ S ∩ A) ∪ (V ∩ S ∩ B) = ((U ∩ A) ∪ (V ∩ B)) ∩ S :=
calc
  (U ∩ S ∩ A) ∪ (V ∩ S ∩ B) 
      = (U ∩ A ∩ S) ∪ (V ∩ S ∩ B) : by rw inter_right_comm
  ... = (U ∩ A ∩ S) ∪ (V ∩ B ∩ S) : by rw inter_right_comm V
  ... = ((U ∩ A) ∪ (V ∩ B)) ∩ S   : by rw union_inter_distrib_right

-- 2ª demostración
example
  {α : Type*} 
  {U V S A B : set α} 
  : (U ∩ S ∩ A) ∪ (V ∩ S ∩ B) = ((U ∩ A) ∪ (V ∩ B)) ∩ S :=
begin 
  rw inter_right_comm, 
  rw inter_right_comm V, 
  rw union_inter_distrib_right
end

-- 3ª demostración
example
  {α : Type*} 
  {U V S A B : set α} 
  : (U ∩ S ∩ A) ∪ (V ∩ S ∩ B) = ((U ∩ A) ∪ (V ∩ B)) ∩ S :=
by rw [inter_right_comm, inter_right_comm V, union_inter_distrib_right]

-- 4ª demostración
example
  {α : Type*} 
  {U V S A B : set α} 
  : (U ∩ S ∩ A) ∪ (V ∩ S ∩ B) = ((U ∩ A) ∪ (V ∩ B)) ∩ S :=
begin 
  ext, 
  simp, 
  tauto!
end

-- 5ª demostración
example
  {α : Type*} 
  {U V S A B : set α} 
  : (U ∩ S ∩ A) ∪ (V ∩ S ∩ B) = ((U ∩ A) ∪ (V ∩ B)) ∩ S :=
by { ext, simp, tauto! }
