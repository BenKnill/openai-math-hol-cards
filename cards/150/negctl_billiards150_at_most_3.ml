(* ========================================================================= *)
(* NEGATIVE CONTROL for billiards150_corner.ml (family 150). Must FAIL.      *)
(* Same lemmas, then the false claim that a one-radian corner allows at most *)
(* 3 wall crossings, i.e. ceil(pi/alpha) - 1 (the main leaf exhibits 4: k = *)
(* 0..3 with t0 = -1/10), with the tactic that proves "at most 4".           *)
(* ========================================================================= *)

let MULTIPLES_IN_OPEN_INTERVAL = prove
 (`!alpha t0 L s.
     &0 < alpha /\ &0 < L /\
     (!k. k IN s ==> t0 < &k * alpha /\ &k * alpha < t0 + L)
     ==> FINITE s /\ &(CARD s) < L / alpha + &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* c = least natural with L <= c * alpha *)
  SUBGOAL_THEN `?c:num. (L:real) <= &c * alpha /\ !j:num. j < c ==> &j * alpha < L`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `\c. L <= &c * alpha` num_WOP) THEN
    REWRITE_TAC[REAL_NOT_LE] THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN ANTS_TAC THENL
     [MP_TAC(SPEC `(L:real) / alpha` REAL_ARCH_SIMPLE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ];
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(c:num) < (L:real) / alpha + &1` ASSUME_TAC THENL
   [ASM_CASES_TAC `c = 0` THENL
     [ASM_REWRITE_TAC[] THEN MP_TAC(SPECL [`L:real`; `alpha:real`] REAL_LT_DIV) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `~(c = 0) ==> 1 <= c`] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s:num->bool = {}` THENL
   [ASM_REWRITE_TAC[FINITE_EMPTY; CARD_CLAUSES] THEN
    MP_TAC(SPECL [`L:real`; `alpha:real`] REAL_LT_DIV) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* m = least element of s *)
  SUBGOAL_THEN `?m:num. m IN (s:num->bool) /\ !k. k IN s ==> m <= k`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `\m:num. m IN s` num_WOP) THEN REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:num->bool) SUBSET IMAGE (\j:num. j + m) {j:num | j < c}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN EXISTS_TAC `k - m:num` THEN
    SUBGOAL_THEN `m <= (k:num)` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&(c:num) * (alpha:real) <= (&(k:num) - &(m:num)) * alpha`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_OF_NUM_SUB; REAL_OF_NUM_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `(t0:real) < &(m:num) * alpha /\ &(k:num) * alpha < t0 + L`
    MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (IMAGE (\j:num. j + m) {j:num | j < c})` ASSUME_TAC THENL
   [SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `IMAGE (\j:num. j + m) {j:num | j < c}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&c:real` THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (\j:num. j + m) {j:num | j < c})` THEN
  ASM_SIMP_TAC[CARD_SUBSET] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN
  SIMP_TAC[CARD_IMAGE_LE; FINITE_NUMSEG_LT]);;

(* Headline: the corner-bounce count, with L = pi.                          *)
let T150_CORNER_BOUNCE_COUNT = prove
 (`!alpha t0 s.
     &0 < alpha /\
     (!k. k IN s ==> t0 < &k * alpha /\ &k * alpha < t0 + pi)
     ==> FINITE s /\ &(CARD s) < pi / alpha + &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MULTIPLES_IN_OPEN_INTERVAL THEN
  EXISTS_TAC `t0:real` THEN ASM_REWRITE_TAC[PI_POS]);;

let PI_BOUNDS_150 = prove
 (`&31 / &10 < pi /\ pi < &32 / &10`,
  MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let NEGCTL_T150_ONE_RADIAN_AT_MOST_3 = prove
 (`!t0 s. (!k. k IN s ==> t0 < &k * &1 /\ &k * &1 < t0 + pi)
          ==> CARD s <= 3`,
  MP_TAC PI_BOUNDS_150 THEN STRIP_TAC THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&1:real`; `t0:real`; `s:num->bool`] T150_CORNER_BOUNCE_COUNT) THEN
  ASM_REWRITE_TAC[REAL_LT_01; REAL_DIV_1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&(CARD(s:num->bool)) < &5` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC]);;
