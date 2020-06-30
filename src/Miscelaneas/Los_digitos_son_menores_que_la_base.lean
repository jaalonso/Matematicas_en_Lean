import data.nat.digits


-- Los dígitos de n en base b son menosres que b.
lemma digits_lt_base 
  (b : ℕ) 
  (hb : 2 ≤ b) 
  (n : ℕ) 
  : ∀ d ∈ digits b n, d < b :=
begin
  cases b with b, 
  { linarith }, 
  { cases b with b, 
    { linarith },
    { clear hb,
      apply nat.strong_induction_on n,
      clear n,
      intro n,
      intro IH,
      intro d,
      intro hd,
      unfold digits at hd IH,
      have h := digits_aux_def (b+2) (by linarith) n,
      cases n with n,
      { cases hd }, 
      { replace h := h (nat.zero_lt_succ n),
        rw h at hd,
        cases hd,
        { rw hd,
          exact n.succ.mod_lt (by linarith) },
        { apply IH _ _ d hd,
          apply nat.div_lt_self (nat.succ_pos _),
          linarith }}}},
end

-- Los dígitos de la expresión decimal de un número son menores o
-- iguales que 9.
lemma digits_le_9 
  (n : ℕ) 
  : ∀ (d ∈ (digits 10 n)), d ≤ 9 :=
λ d hd, nat.le_of_lt_succ $ digits_lt_base 10 (by norm_num) n _ hd
