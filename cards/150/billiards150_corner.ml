(* ========================================================================= *)
(* Family 150 of the OpenAI math release: "Ergodicity of triangular          *)
(* billiards with an irrational angle" (September 25, 2026), section 2: a    *)
(* ball entering a corner of angle alpha makes at most ceil(pi / alpha)      *)
(* bounces before it leaves.                                                 *)
(* Profile: heavy (HOL Light's real pi).                                     *)
(*                                                                           *)
(* The classical argument, in two steps:                                     *)
(*  (G) unfolding: reflect the wedge across its walls; the trajectory becomes *)
(*      a straight line, and in polar angle (on the universal cover) that    *)
(*      line sweeps an OPEN interval (t0, t0 + pi) of length exactly pi;     *)
(*      the ball bounces once each time the angle passes a wall copy at an   *)
(*      angle k * alpha (k an integer; shifting k by a constant, k >= 0);    *)
(*  (C) counting: an open interval of length pi contains fewer than          *)
(*      pi/alpha + 1 multiples of alpha, i.e. at most ceil(pi/alpha).        *)
(* Checked here: step (C) only.                                              *)
(*   MULTIPLES_IN_OPEN_INTERVAL  for alpha > 0, L > 0 and any real t0, every *)
(*     set s of naturals with t0 < k alpha < t0 + L for k in s is finite     *)
(*     and has CARD s < L/alpha + 1.                                         *)
(*   T150_CORNER_BOUNCE_COUNT  the same with L = pi (headline):              *)
(*     CARD s < pi/alpha + 1, equivalently CARD s <= ceil(pi/alpha).         *)
(*   T150_ONE_RADIAN  alpha = 1: at most 4 wall angles fit, and 4 do         *)
(*     (k = 0,1,2,3 with t0 = -1/10).                                        *)
(*   T150_POINT_THREE  alpha = 3/10: at most 11 fit, and 11 do               *)
(*     (k = 0..10 with t0 = -1/10).                                          *)
(*   (These match the scout's brute-force counts: 1 rad -> 4, 0.3 rad -> 11.) *)
(*                                                                           *)
(* NOT checked here: step (G), i.e. any billiard dynamics, reflection law or *)
(* unfolding; so HOL does not certify "a ball makes at most ceil(pi/alpha)   *)
(* bounces", only the counting fact that the unfolding argument reduces it   *)
(* to. Nothing about ergodicity (Lean-formalized in the release,             *)
(* lean/docs/150.md) or weak mixing (paper-only).                            *)
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

(* A one-radian corner: at most 4 wall crossings, and 4 occur.              *)
let T150_ONE_RADIAN = prove
 (`(!t0 s. (!k. k IN s ==> t0 < &k * &1 /\ &k * &1 < t0 + pi)
            ==> CARD s <= 4) /\
   (!k. k IN 0..3 ==> --(&1 / &10) < &k * &1 /\
                      &k * &1 < --(&1 / &10) + pi) /\
   CARD(0..3) = 4`,
  MP_TAC PI_BOUNDS_150 THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`&1:real`; `t0:real`; `s:num->bool`] T150_CORNER_BOUNCE_COUNT) THEN
    ASM_REWRITE_TAC[REAL_LT_01; REAL_DIV_1] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&(CARD(s:num->bool)) < &5` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC];
    REWRITE_TAC[IN_NUMSEG] THEN GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= (&k:real) /\ (&k:real) <= &3` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE; LE_0]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[CARD_NUMSEG] THEN ARITH_TAC]);;

(* A 0.3-radian corner: at most 11, and 11 occur.                           *)
let T150_POINT_THREE = prove
 (`(!t0 s. (!k. k IN s ==> t0 < &k * (&3 / &10) /\
                            &k * (&3 / &10) < t0 + pi)
            ==> CARD s <= 11) /\
   (!k. k IN 0..10 ==> --(&1 / &10) < &k * (&3 / &10) /\
                       &k * (&3 / &10) < --(&1 / &10) + pi) /\
   CARD(0..10) = 11`,
  MP_TAC PI_BOUNDS_150 THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`&3 / &10:real`; `t0:real`; `s:num->bool`]
                 T150_CORNER_BOUNCE_COUNT) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
    SUBGOAL_THEN `pi / (&3 / &10) = &10 / &3 * pi` (fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&(CARD(s:num->bool)) < &12` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC];
    REWRITE_TAC[IN_NUMSEG] THEN GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= (&k:real) /\ (&k:real) <= &10` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE; LE_0]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[CARD_NUMSEG] THEN ARITH_TAC]);;
