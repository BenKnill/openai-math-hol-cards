(* ========================================================================= *)
(* NEGATIVE CONTROL for pi355_017.ml (family 017). Must FAIL.                 *)
(* Identical lemmas, then the false claim 1/(355^3 sin^2 355) > 25 (the true  *)
(* value is 24.598; the main leaf proves it is < 24.7), attempted with the    *)
(* same tactic that proves > 24.5 in the main leaf.                           *)
(* ========================================================================= *)

let PI355_GAP = prove
 (`&2664 / &10 pow 10 < &355 / &113 - pi /\
   &355 / &113 - pi < &2669 / &10 pow 10 /\
   abs(pi - &355 / &113) < &27 / &10 pow 8`,
  MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let PI_BETWEEN_3_AND_4 = prove
 (`&3 < pi /\ pi < &4`,
  MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

(* 355 = 113 pi + y with y = 355 - 113 pi, and cos(113 pi) = -1.            *)
let SIN_355_EQ = prove
 (`sin(&355) = --sin(&355 - &113 * pi)`,
  MP_TAC(SPECL [`&355 - &113 * pi`; `&113 * pi`] SIN_ADD) THEN
  REWRITE_TAC[SIN_NPI; COS_NPI; REAL_ARITH `(a - b) + b:real = a`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* Lower bound for sin near 0 from HOL Light's Taylor bound TAYLOR_CSIN    *)
(* (n = 0): |sin y - y| <= |y|^3 / 2.                                       *)
let SIN_SMALL_LOWER = prove
 (`!y. &0 <= y ==> y - y pow 3 / &2 <= sin y`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`0`; `Cx(y)`] TAYLOR_CSIN) THEN
  REWRITE_TAC[VSUM_SING_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[COMPLEX_DIV_1; COMPLEX_POW_1; complex_pow] THEN
  REWRITE_TAC[COMPLEX_MUL_LID; GSYM CX_SIN; GSYM CX_SUB] THEN
  REWRITE_TAC[IM_CX; COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_EXP_0] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= y ==> abs y = y`] THEN REAL_ARITH_TAC);;

let SIN_355_BOUNDS = prove
 (`--(&302 / &10 pow 7) < sin(&355) /\ sin(&355) < --(&301 / &10 pow 7)`,
  REWRITE_TAC[SIN_355_EQ] THEN
  MP_TAC(SPEC `&355 - &113 * pi` REAL_ABS_SIN_BOUND_LE) THEN
  MP_TAC(SPEC `&355 - &113 * pi` SIN_SMALL_LOWER) THEN
  MP_TAC PI355_GAP THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  STRIP_TAC THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&355 - &113 * pi) pow 3 <= (&302 / &10000000) pow 3`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC);;

let NEGCTL_FLINT_HILLS_355_TERM_GT_25 = prove
 (`&25 < inv(&355 pow 3 * sin(&355) pow 2)`,
  MP_TAC SIN_355_BOUNDS THEN SPEC_TAC(`sin(&355)`,`s:real`) THEN
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&301 / &10 pow 7) pow 2 < s pow 2 /\
                s pow 2 < (&302 / &10 pow 7) pow 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&355 pow 3 * s pow 2`; `inv(&25)`] REAL_LT_INV2) THEN
  REWRITE_TAC[REAL_INV_INV] THEN DISCH_THEN MATCH_MP_TAC THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;
