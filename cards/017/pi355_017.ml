(* ========================================================================= *)
(* Family 017 of the OpenAI math release: "The irrationality exponent of pi  *)
(* is 2" (September 24, 2026). The hook of the pi film: the n = 355 spike in  *)
(* the Flint-Hills series  sum_n 1 / (n^3 sin^2 n).                          *)
(* Profile: heavy (Multivariate/realanalysis.ml: HOL Light's real pi, sin).   *)
(*                                                                            *)
(* Checked here, about HOL Light's own pi and sin (no new definitions):       *)
(*   PI355_GAP        2.664e-7 < 355/113 - pi < 2.669e-7, hence               *)
(*                    |pi - 355/113| < 2.7e-7   (true value 2.6676e-7).       *)
(*   SIN_355_BOUNDS   -3.02e-5 < sin 355 < -3.01e-5  (true -3.0144e-5), via   *)
(*                    sin 355 = -sin(355 - 113 pi) and y - y^3/2 <= sin y     *)
(*                    <= |y| for the small y = 355 - 113 pi > 0.              *)
(*   FLINT_HILLS_355_TERM   24.5 < 1/(355^3 sin^2 355) < 24.7  (true 24.598). *)
(*   FLINT_HILLS_PARTIAL_355  sum_{n=1}^{355} 1/(n^3 sin^2 n) > 24, since     *)
(*                    every term is >= 0 and the n = 355 term alone is > 24.  *)
(*   PI355_CERTIFICATE  the conjunction of the above (the card's headline).   *)
(* The only pi input is HOL Light's own PI_APPROX_32,                         *)
(* |pi - 13493037705/2^32| <= 2^-32, proved in Multivariate/                  *)
(* transcendentals.ml from a Taylor bound for sin(pi/6) = 1/2. The sin facts  *)
(* used are SIN_ADD, SIN_NPI, COS_NPI, SIN_POS_PI, REAL_ABS_SIN_BOUND_LE and  *)
(* TAYLOR_CSIN (n = 0).                                                       *)
(*                                                                            *)
(* NOT checked here: that the Flint-Hills series converges (the paper's       *)
(* corollary; paper-only: the release's Lean covers mu(pi) = 2 and says       *)
(* Flint-Hills is outside its selected statement); anything about the         *)
(* irrationality exponent; the partial sum through n = 354 (about 4.807),     *)
(* which would need a lower bound on |sin n| for every n <= 354.              *)
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

(* Headline: the n = 355 term of the Flint-Hills series lies in (24.5, 24.7) *)
let FLINT_HILLS_355_TERM = prove
 (`&24 < inv(&355 pow 3 * sin(&355) pow 2) /\
   &245 / &10 < inv(&355 pow 3 * sin(&355) pow 2) /\
   inv(&355 pow 3 * sin(&355) pow 2) < &247 / &10`,
  MP_TAC SIN_355_BOUNDS THEN SPEC_TAC(`sin(&355)`,`s:real`) THEN
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&301 / &10 pow 7) pow 2 < s pow 2 /\
                s pow 2 < (&302 / &10 pow 7) pow 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&245 / &10 < x /\ x < &247 / &10
    ==> &24 < x /\ &245 / &10 < x /\ x < &247 / &10`) THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`&355 pow 3 * s pow 2`; `inv(&245 / &10)`] REAL_LT_INV2);
    MP_TAC(SPECL [`inv(&247 / &10)`; `&355 pow 3 * s pow 2`] REAL_LT_INV2)]
  THEN REWRITE_TAC[REAL_INV_INV] THEN DISCH_THEN MATCH_MP_TAC THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* The partial sum through n = 355 exceeds 24: every term is >= 0.          *)
let FLINT_HILLS_PARTIAL_355 = prove
 (`&24 < sum(1..355) (\n. inv(&n pow 3 * sin(&n) pow 2))`,
  MP_TAC(ISPECL [`1`; `354`; `\n. inv(&n pow 3 * sin(&n) pow 2)`]
                SUM_POS_LE_NUMSEG) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. inv(&n pow 3 * sin(&n) pow 2)`; `1`; `355`]
                SUM_CLAUSES_RIGHT) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN
  MP_TAC FLINT_HILLS_355_TERM THEN REAL_ARITH_TAC);;

(* The card's one-line summary, as a single theorem.                        *)
let PI355_CERTIFICATE = prove
 (`abs(pi - &355 / &113) < &27 / &10 pow 8 /\
   --(&302 / &10 pow 7) < sin(&355) /\ sin(&355) < --(&301 / &10 pow 7) /\
   &245 / &10 < inv(&355 pow 3 * sin(&355) pow 2) /\
   inv(&355 pow 3 * sin(&355) pow 2) < &247 / &10 /\
   &24 < sum(1..355) (\n. inv(&n pow 3 * sin(&n) pow 2))`,
  REWRITE_TAC[PI355_GAP; SIN_355_BOUNDS; FLINT_HILLS_355_TERM;
              FLINT_HILLS_PARTIAL_355]);;
