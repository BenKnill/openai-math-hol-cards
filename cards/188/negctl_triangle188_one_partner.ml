(* ========================================================================= *)
(* NEGATIVE CONTROL for triangle188.ml (family 188). Must FAIL.               *)
(* "One partner" version of Spencer's law: claims q' = -D q^2 for             *)
(* q(t) = (1 + 2 D t)^(-1/2), with the same tactic that proves q' = -D q^3.   *)
(* (dq/dt = -D q^2 would be the law if a triangle needed only one other edge  *)
(* alive; its solution is 1/(1 + D t), not (1 + 2 D t)^(-1/2).)               *)
(* ========================================================================= *)

let TR188_Q_AT_0 = prove
 (`!D. inv(sqrt(&1 + &2 * D * &0)) = &1`,
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; SQRT_1; REAL_INV_1]);;

let TR188_SURVIVAL_ODE = prove
 (`!D x. &0 <= D /\ &0 <= x
         ==> ((\t. inv(sqrt(&1 + &2 * D * t))) has_real_derivative
              (--D * inv(sqrt(&1 + &2 * D * x)) pow 3)) (atreal x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + &2 * D * x` ASSUME_TAC THENL
   [MP_TAC(SPECL [`D:real`; `x:real`] REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&1 + &2 * D * x)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  REAL_DIFF_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
  UNDISCH_TAC `&0 < sqrt(&1 + &2 * D * x)` THEN
  SPEC_TAC(`sqrt(&1 + &2 * D * x)`,`q:real`) THEN
  CONV_TAC REAL_FIELD);;

let NEGCTL_TR188_ONE_PARTNER_LAW = prove
 (`!D x. &0 <= D /\ &0 <= x
         ==> ((\t. inv(sqrt(&1 + &2 * D * t))) has_real_derivative
              (--D * inv(sqrt(&1 + &2 * D * x)) pow 2)) (atreal x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + &2 * D * x` ASSUME_TAC THENL
   [MP_TAC(SPECL [`D:real`; `x:real`] REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&1 + &2 * D * x)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  REAL_DIFF_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
  UNDISCH_TAC `&0 < sqrt(&1 + &2 * D * x)` THEN
  SPEC_TAC(`sqrt(&1 + &2 * D * x)`,`q:real`) THEN
  CONV_TAC REAL_FIELD);;
