theorem facil : 2 + 2 = 4 := rfl

#check facil
-- | facil : 2 + 2 = 4

def ultimo_teorema_de_Fermat :=
  ∀ x y z n : ℕ, n > 2 → x * y * z ≠ 0 → x^n + y^n ≠ z^n

theorem dificil : ultimo_teorema_de_Fermat := sorry
-- | declaration 'dificil' uses sorry

#check dificil
-- | dificil : ultimo_teorema_de_Fermat
