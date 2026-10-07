(* ========================================================================= *)
(* NEGATIVE CONTROL written for openai-math-hol-cards (2026-10-07).         *)
(* Family 028: the same claim without the hypothesis ~(s = {}).              *)
(* False: the empty set is invariant under every translation.                *)
(* It reuses the leaf's tactic on a FALSE variant. Expected: FAILED.      *)
(* ========================================================================= *)

let NEGCTL_M028_EMPTY_SET_ALLOWED = prove
 (`!s:(real#real)->bool a b.
     FINITE s /\
     IMAGE (\z. (FST z + a, SND z + b)) s = s
     ==> a = &0 /\ b = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(&(CARD(s:(real#real)->bool)) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_MESON_TAC[CARD_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN s /\ y IN s /\
          (\z:real#real. (FST z + a, SND z + b)) x =
          (\z:real#real. (FST z + a, SND z + b)) y ==> x = y`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN
    SIMP_TAC[REAL_EQ_ADD_RCANCEL]; ALL_TAC] THEN
  FIRST_ASSUM(fun inj ->
    MP_TAC(MATCH_MP (ISPECL [`\z:real#real. (FST z + a, SND z + b)`;
                             `FST:real#real->real`;
                             `s:(real#real)->bool`] SUM_IMAGE) inj) THEN
    MP_TAC(MATCH_MP (ISPECL [`\z:real#real. (FST z + a, SND z + b)`;
                             `SND:real#real->real`;
                             `s:(real#real)->bool`] SUM_IMAGE) inj)) THEN
  ASM_REWRITE_TAC[o_DEF] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_CONST; ETA_AX] THEN
  REWRITE_TAC[REAL_ARITH `x = x + y <=> y = &0`; REAL_ENTIRE] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;
