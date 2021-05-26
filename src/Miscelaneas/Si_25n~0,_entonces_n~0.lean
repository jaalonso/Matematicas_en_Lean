import tactic

-- set_option pp.all true

example
  (n : ℤ)
  (hn : 25 * n = n)
  : n = 0 :=
begin
  have h := sub_eq_zero.mpr hn, -- internally an awkward `0`
  -- h : 25 * n - n = 0
  ring at *, -- `h` now has a better `0`
  -- h : 25 * n - n = 0
  ring at *,
  -- h : 24 * n = 0
  linarith,
end
