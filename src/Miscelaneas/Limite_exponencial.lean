-- Límite exponencial
-- ==================

-- ----------------------------------------------------
-- Ejercicio. Demostrar que si C > 0, entonces
--    lim (C^(1/n)) = 1
-- ----------------------------------------------------

import analysis.special_functions.pow

lemma tendsto_root_at_top_nhds_1_of_pos
  {C: ℝ}
  (c_pos: C > 0)
  : filter.tendsto (λ (n : ℕ), C^((1 : ℝ) / n)) filter.at_top (nhds 1) :=
begin
  have h_exp_form: (λ (n : ℕ), C^((1 : ℝ) / n)) = (λ (n: ℕ), real.exp((real.log C) / n)),
  { ext,
    simp,
    rw div_eq_mul_inv,
    rw real.exp_mul,
    rw real.exp_log c_pos, },
  { rw h_exp_form,
    apply filter.tendsto.comp,
    apply real.tendsto_exp_nhds_0_nhds_1,
    apply tendsto_const_div_at_top_nhds_0_nat, }
end
