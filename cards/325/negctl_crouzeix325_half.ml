(* ========================================================================= *)
(* NEGATIVE CONTROL written for openai-math-hol-cards (2026-10-07).         *)
(* Family 325: claims |2xy| <= 1/2 when x^2 + y^2 = 1.                       *)
(* False at x = y = 1/sqrt(2), where 2xy = 1.                                *)
(* It reuses the leaf's tactic on a FALSE variant. Expected: FAILED.      *)
(* ========================================================================= *)

let NEGCTL_C325_TWO_XY_HALF = prove
 (`!x y. x pow 2 + y pow 2 = &1 ==> abs(&2 * x * y) <= &1 / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_BOUNDS] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `&0 <= (x + y) pow 2 ==> --(x pow 2 + y pow 2) <= &2 * x * y`);
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= (x - y) pow 2 ==> &2 * x * y <= x pow 2 + y pow 2`)] THEN
  REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]);;
