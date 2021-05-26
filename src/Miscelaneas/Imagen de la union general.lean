-- Imagen de la unión general
-- ==========================

import tactic

-- 1ª demostración
example
  {α β : Type*}
  {f : α → β}
  {s : set α}
  : f '' ((⋃ i ∈ s, {i}) ) = (⋃ i ∈ s, f '' {i}) :=
begin
  ext,
  split,
  { finish, },
  { finish, },
end

-- 2ª demostración
example
  {α β : Type*}
  {f : α → β}
  {s : set α}
  : f '' ((⋃ i ∈ s, {i}) ) = (⋃ i ∈ s, f '' {i}) :=
by ext; simp [eq_comm]

-- 3ª demostración
example
  {α β : Type*}
  {f : α → β}
  {s : set α}
  : f '' ((⋃ i ∈ s, {i}) ) = (⋃ i ∈ s, f '' {i}) :=
by tidy
