import tactic

namespace hidden

definition cong (a b m : ℤ) : Prop := ∃ n : ℤ, b - a = m * n

notation a ` ≡ ` b ` mod ` m  := cong a b m

-- Con squeeze_simp

example
  (m : ℤ)
  : ∀ a : ℤ, a ≡ a mod m :=
begin
 intro a,
 unfold cong,
 existsi (0:ℤ),
 squeeze_simp,
end

-- Da la sugerencia
--   Try this: simp only [mul_zero, sub_self]

set_option trace.simplify true

example
  (m : ℤ)
  : ∀ a : ℤ, a ≡ a mod m :=
begin
 intro a,
 unfold cong,
 existsi (0:ℤ),
 simp,
end

set_option trace.simplify false

example
  (m : ℤ)
  : ∀ a : ℤ, a ≡ a mod m :=
begin
 intro a,
 unfold cong,
 existsi (0:ℤ),
 simp,
end

set_option trace.simplify.rewrite true

example
  (m : ℤ)
  : ∀ a : ℤ, a ≡ a mod m :=
begin
 intro a,
 unfold cong,
 existsi (0:ℤ),
 simp,
end

end hidden

-- Referencia
-- + "Simp" https://bit.ly/3hDPVGz
