import data.set.basic
import data.real.basic
import topology.basic

open set
open function

variables (α β : Type) [fintype β]

example  
  (A : set α) 
  (H : ∃ (f : α → β), inj_on f A) 
  : finite A :=
begin
   cases H with f hf,
   have h0 := finite.of_fintype (image f A),
   exact finite_of_finite_image hf h0,
end
