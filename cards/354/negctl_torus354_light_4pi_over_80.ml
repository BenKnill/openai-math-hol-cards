(* ========================================================================= *)
(* NEGATIVE CONTROL written for openai-math-hol-cards (2026-10-07).         *)
(* Family 354 (light): the ball-tube switch claimed at 4 PI/80, not 4 PI/81. *)
(* False for V strictly between 4 PI/81 and 4 PI/80.                         *)
(* It reuses the leaf's tactic on a FALSE variant. Expected: FAILED.      *)
(* ========================================================================= *)

let T354_POW_LE_EQ = prove
 (`!n x y. ~(n = 0) /\ &0 <= x /\ &0 <= y ==> (x pow n <= y pow n <=> x <= y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LE] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]]);;

let NEGCTL_T354_BALL_TUBE_SWITCH_4PI_OVER_80 = prove
 (`!PI V b t.
     &0 < PI /\ &0 < V /\ &0 <= b /\ &0 <= t /\
     b pow 3 = &36 * PI * V pow 2 /\ t pow 2 = &4 * PI * V
     ==> (b <= t <=> V <= &4 * PI / &80)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`6`; `b:real`; `t:real`] T354_POW_LE_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `b pow 6 = (b pow 3) pow 2 /\ t pow 6 = (t pow 2) pow 3`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &16 * PI pow 2 * V pow 3` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT; REAL_ARITH `&0 < &16`];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(&16 * PI pow 2 * V pow 3) * (&81 * V) <=
              (&16 * PI pow 2 * V pow 3) * (&4 * PI)` THEN
  CONJ_TAC THENL
   [BINOP_TAC THEN CONV_TAC REAL_RING;
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN ASM_REAL_ARITH_TAC]);;

