import tactic
open list
open multiset

-- #print notation (~)
-- #print perm

example
  { α: Type }
  (as bs cs ds: list α)
  : (as ++ bs ++ cs ++ ds) ~ (ds ++ bs ++ cs ++ as) :=
calc (as ++ bs ++ cs ++ ds)
     ~ as ++ (bs ++ cs ++ ds)   : by simp only [append_assoc]
 ... ~ (bs ++ cs ++ ds) ++ as   : perm_append_comm
 ... ~ (bs ++ (cs ++ ds)) ++ as : by simp only [append_assoc]
 ... ~ (bs ++ (ds ++ cs)) ++ as : perm.append_right _ $ perm.append_left _ perm_append_comm
 ... ~ (bs ++ ds ++ cs) ++ as   : by simp only [append_assoc]
 ... ~ (ds ++ bs ++ cs ++ as)   : perm.append_right _ $ perm.append_right _ perm_append_comm

example
  { α: Type }
  (as bs cs ds: list α)
  : (as ++ bs ++ cs ++ ds) ~ (ds ++ bs ++ cs ++ as) :=
begin
  rw ← coe_eq_coe,
  simp only [← coe_add],
  abel,
end

example
  {α}
  (as bs cs ds : list α)
  : (as ++ bs ++ cs ++ ds).nodup ↔ (ds ++ bs ++ cs ++ as).nodup :=
begin
  apply perm.nodup_iff,
  rw ← coe_eq_coe,
  simp only [← coe_add, add_left_comm, add_comm],
end
