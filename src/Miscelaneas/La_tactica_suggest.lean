import tactic

-- example (n : nat) : n < n + 1 :=
-- begin
--   suggest,
--   sorry
-- end

example (n : nat) : n < n + 1 :=
by exact lt_add_one n

-- Al colocar el cursor sobre suggest muestra las siguientes sugerencias
--    Try this: exact lt_add_one n
--    Try this: exact nat.lt.base n
--    Try this: exact nat.lt_succ_self n
--    Try this: refine not_le.mp _
--    Try this: refine gt_iff_lt.mp _
--    Try this: refine nat.lt.step _
--    Try this: refine set.mem_Ioi.mp _
--    Try this: refine set.mem_Iio.mp _
--    Try this: refine lt_of_not_ge _
--    Try this: refine bit1_lt_bit1.mp _
--    Try this: refine bit0_lt_bit0.mp _
--    Try this: refine lt_of_not_ge' _
--    Try this: refine (lt_iff_not_ge n (n + 1)).mpr _
--    Try this: refine list.mem_range.mp _
--    Try this: refine int.coe_nat_lt.mp _
--    Try this: refine lt_iff_not_ge'.mpr _
--    Try this: refine n.lt_add_left 1 n _
--    Try this: refine nat.lt_succ_iff.mpr _
--    Try this: refine enat.coe_lt_coe.mp _
--    Try this: refine nat.succ_le_iff.mp _
--    Try this: refine lt_iff_le_not_le.mpr _
--    Try this: refine set.nonempty_Ico.mp _
--    Try this: refine set.nonempty_Ioc.mp _
--    Try this: refine set.left_mem_Ico.mp _
--    Try this: refine lt_iff_le_and_ne.mpr _
--    Try this: refine finset.mem_range.mp _
--    Try this: refine n.lt_add_right n 1 _
--    Try this: refine (n.psub_eq_none (n + 1)).mp _
--    Try this: refine (nat.fact_lt _).mp _
--    Try this: refine lt_of_le_of_ne _ _
--    Try this: refine lt_of_le_not_le _ _
--    Try this: refine buffer.lt_aux_1 _
--    Try this: refine lt_of_le_of_ne' _ _
--    Try this: refine gt.trans _ _
--    Try this: refine lt.trans _ _
--    Try this: refine lt_trans _ _
--    Try this: refine gt_trans _ _
--    Try this: refine nat.lt_trans _ _
--    Try this: refine (lt_is_glb_iff _).mpr _
--    Try this: refine (is_glb_lt_iff _).mpr _
--    Try this: refine (is_lub_lt_iff _).mpr _
--    Try this: refine (lt_is_lub_iff _).mpr _
--    Try this: refine (pnat.mk_lt_mk n (n + 1) _ _).mp _
--    Try this: refine gt_of_ge_of_gt _ _
--    Try this: refine gt_of_gt_of_ge _ _
--    Try this: refine lt_of_lt_of_le _ _
--    Try this: refine lt_of_le_of_lt _ _
--    Try this: refine (mul_lt_mul_left _).mp _
--    Try this: refine forall_lt_iff_le.mpr _ _
--    Try this: refine (mul_lt_mul_right _).mp _

-- Referencia:
-- Ver https://bit.ly/2Vkvrsu
