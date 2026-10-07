(* ========================================================================= *)
(* NEGATIVE CONTROL for hotspots369_bessel_deriv.ml (family 369). Must FAIL. *)
(* Same definitions and lemmas, then the plausible slip "J_1' = J_0" at the  *)
(* level of terms: d/dx of the k-th J_1 term claimed to be the k-th J_0 term *)
(* (the truth is the k-th term of J_0 - J_1/x), with the same tactic that    *)
(* proves BESSEL_J1_TERM_DERIV.                                              *)
(* ========================================================================= *)

let bessel_j0_term = new_definition
 `bessel_j0_term (x:real) k =
    (--(&1)) pow k * (x pow 2 / &4) pow k / (&(FACT k) * &(FACT k))`;;

let bessel_j1_term = new_definition
 `bessel_j1_term (x:real) k =
    (--(&1)) pow k * (x / &2) * (x pow 2 / &4) pow k /
    (&(FACT k) * &(FACT(SUC k)))`;;

let bessel_dj1_term = new_definition
 `bessel_dj1_term (x:real) k =
    (--(&1)) pow k * (&2 * &k + &1) * (x pow 2 / &4) pow k /
    (&2 * &(FACT k) * &(FACT(SUC k)))`;;

let bessel_j0 = new_definition
 `bessel_j0 (x:real) = real_infsum (from 0) (bessel_j0_term x)`;;

let bessel_j1 = new_definition
 `bessel_j1 (x:real) = real_infsum (from 0) (bessel_j1_term x)`;;

let bessel_dj1 = new_definition
 `bessel_dj1 (x:real) = bessel_j0 x - bessel_j1 x / x`;;

(* ------------------------------------------------------------------------- *)
(* Term recurrences.                                                         *)
(* ------------------------------------------------------------------------- *)

let BESSEL_STEP_TAC defn =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[defn; FACT; real_pow; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_SUC] THEN
  MP_TAC(SPEC `k:num` FACT_NZ) THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
  MP_TAC(SPEC `k:num` REAL_POS) THEN
  SPEC_TAC(`&(FACT k)`,`f:real`) THEN SPEC_TAC(`&k`,`n:real`) THEN
  SPEC_TAC(`(--(&1)) pow k`,`s:real`) THEN
  SPEC_TAC(`(x pow 2 / &4) pow k`,`p:real`) THEN
  CONV_TAC REAL_FIELD;;

let BESSEL_J0_STEP = prove
 (`!x k. bessel_j0_term x (SUC k) =
         bessel_j0_term x k * (--(x pow 2 / &4) / ((&k + &1) * (&k + &1)))`,
  BESSEL_STEP_TAC bessel_j0_term);;

let BESSEL_J1_STEP = prove
 (`!x k. bessel_j1_term x (SUC k) =
         bessel_j1_term x k * (--(x pow 2 / &4) / ((&k + &1) * (&k + &2)))`,
  BESSEL_STEP_TAC bessel_j1_term);;

let BESSEL_DJ1_STEP = prove
 (`!x k. bessel_dj1_term x (SUC k) =
         bessel_dj1_term x k *
         (--(x pow 2 / &4) /
          (((&2 * &k + &1) * (&k + &1) * (&k + &2)) / (&2 * &k + &3)))`,
  BESSEL_STEP_TAC bessel_dj1_term);;

let BESSEL_COMBINE = prove
 (`!x k. ~(x = &0)
         ==> bessel_j0_term x k - bessel_j1_term x k / x = bessel_dj1_term x k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bessel_j0_term; bessel_j1_term; bessel_dj1_term; FACT;
              GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_SUC] THEN
  MP_TAC(SPEC `k:num` FACT_NZ) THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
  MP_TAC(SPEC `k:num` REAL_POS) THEN
  SPEC_TAC(`&(FACT k)`,`f:real`) THEN SPEC_TAC(`&k`,`n:real`) THEN
  SPEC_TAC(`(--(&1)) pow k`,`s:real`) THEN
  SPEC_TAC(`(x pow 2 / &4) pow k`,`p:real`) THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Summability by the ratio test.                                            *)
(* ------------------------------------------------------------------------- *)

let RATIO_SUMMABLE = prove
 (`!a r N. (!k. N <= k ==> a(SUC k) = a k * r k /\ abs(r k) <= &1 / &2)
           ==> real_summable (from 0) (a:num->real)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_summable] THEN
  MATCH_MP_TAC REAL_SERIES_RATIO THEN
  MAP_EVERY EXISTS_TAC [`&1 / &2`; `N:num`] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GE] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
  MP_TAC(SPECL [`abs((a:num->real) n)`; `abs((r:num->real) n)`; `&1 / &2`]
               REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC);;

let RATIO_BOUND = prove
 (`!x d. abs x <= &2 /\ &2 <= d ==> abs(--(x pow 2 / &4) / d) <= &1 / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x pow 2 <= &4` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs x pow 2 <= &2 pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW2_ABS] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_DIV] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&2 <= d ==> &0 < abs d`] THEN
  MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC);;

let BESSEL_J0_SUMMABLE = prove
 (`!x. abs x <= &2 ==> real_summable (from 0) (bessel_j0_term x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RATIO_SUMMABLE THEN
  MAP_EVERY EXISTS_TAC
   [`\k. --(x pow 2 / &4) / ((&k + &1) * (&k + &1))`; `1`] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[BESSEL_J0_STEP] THEN
  MATCH_MP_TAC RATIO_BOUND THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 <= &k` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  MP_TAC(SPEC `&k` REAL_LE_SQUARE) THEN REAL_ARITH_TAC);;

let BESSEL_J1_SUMMABLE = prove
 (`!x. abs x <= &2 ==> real_summable (from 0) (bessel_j1_term x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RATIO_SUMMABLE THEN
  MAP_EVERY EXISTS_TAC
   [`\k. --(x pow 2 / &4) / ((&k + &1) * (&k + &2))`; `0`] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[BESSEL_J1_STEP] THEN
  MATCH_MP_TAC RATIO_BOUND THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `&k` REAL_LE_SQUARE) THEN MP_TAC(SPEC `k:num` REAL_POS) THEN
  REAL_ARITH_TAC);;

let BESSEL_DJ1_SUMS = prove
 (`!x. ~(x = &0) /\ abs x <= &2
       ==> (bessel_dj1_term x real_sums bessel_dj1 x) (from 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bessel_dj1; bessel_j0; bessel_j1] THEN
  SUBGOAL_THEN
   `bessel_dj1_term x = (\k. bessel_j0_term x k - bessel_j1_term x k / x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_SIMP_TAC[BESSEL_COMBINE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_SERIES_SUB THEN CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[REAL_SUMS_INFSUM; BESSEL_J0_SUMMABLE];
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_SERIES_RMUL THEN
    REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[REAL_SUMS_INFSUM; BESSEL_J1_SUMMABLE]]);;

(* ------------------------------------------------------------------------- *)
(* Alternating structure of the J_1' series from k = 2 on.                   *)
(* ------------------------------------------------------------------------- *)

let BESSEL_DJ1_MONO = prove
 (`!x k. abs x <= &2 /\ 1 <= k
         ==> abs(bessel_dj1_term x (SUC k)) <= abs(bessel_dj1_term x k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BESSEL_DJ1_STEP; REAL_ABS_MUL] THEN
  MP_TAC(SPECL [`x:real`;
    `((&2 * &k + &1) * (&k + &1) * (&k + &2)) / (&2 * &k + &3)`] RATIO_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &2 * &k + &3` ASSUME_TAC THENL
     [MP_TAC(SPEC `k:num` REAL_POS) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    SUBGOAL_THEN `&1 <= &k` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &k * (&k - &1) /\ &0 <= &k * &k * &k`
    MP_TAC THENL
     [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`abs(bessel_dj1_term x k)`;
                `abs(--(x pow 2 / &4) /
                  (((&2 * &k + &1) * (&k + &1) * (&k + &2)) / (&2 * &k + &3)))`;
                `&1 / &2`] REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS] THEN
  MP_TAC(SPEC `bessel_dj1_term x k` REAL_ABS_POS) THEN REAL_ARITH_TAC);;

let BESSEL_DJ1_MAGNITUDE_POS = prove
 (`!x k. &0 <= (&2 * &k + &1) * (x pow 2 / &4) pow k /
              (&2 * &(FACT k) * &(FACT(SUC k)))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MP_TAC(SPEC `k:num` REAL_POS) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
    SIMP_TAC[REAL_LE_MUL; REAL_POS]]);;

let BESSEL_DJ1_SIGNS = prove
 (`!x k. (EVEN k ==> &0 <= bessel_dj1_term x k) /\
         (ODD k ==> bessel_dj1_term x k <= &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bessel_dj1_term; REAL_POW_NEG; REAL_POW_ONE;
                                  GSYM NOT_EVEN] THEN
  MP_TAC(SPECL [`x:real`; `k:num`] BESSEL_DJ1_MAGNITUDE_POS) THEN
  ASM_CASES_TAC `EVEN k` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Partial-sum bounds (alternating series, HOL's ALTERNATING_SUM_BOUNDS).     *)
(* ------------------------------------------------------------------------- *)

let BESSEL_DJ1_PARTIAL_BOUNDS = prove
 (`!x M. ~(x = &0) /\ abs x <= &2
         ==> (ODD M
              ==> sum(0..1) (bessel_dj1_term x) +
                  sum(0..M) (\n. bessel_dj1_term x (n + 2)) <= bessel_dj1 x) /\
             (EVEN M
              ==> bessel_dj1 x <=
                  sum(0..1) (bessel_dj1_term x) +
                  sum(0..M) (\n. bessel_dj1_term x (n + 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `e = \n. bessel_dj1_term x (n + 2)` THEN
  SUBGOAL_THEN
   `!m n. (EVEN m ==> &0 <= sum(m..n) e /\ sum(m..n) e <= e m) /\
          (ODD m ==> e m <= sum(m..n) e /\ sum(m..n) e <= &0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ALTERNATING_SUM_BOUNDS THEN EXPAND_TAC "e" THEN
    REWRITE_TAC[ARITH_RULE `SUC n + 2 = SUC(n + 2)`] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `n:num` THENL
     [MATCH_MP_TAC BESSEL_DJ1_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      DISCH_TAC THEN MATCH_MP_TAC(CONJUNCT1(SPEC_ALL BESSEL_DJ1_SIGNS)) THEN
      ASM_REWRITE_TAC[EVEN_ADD; ARITH];
      DISCH_TAC THEN MATCH_MP_TAC(CONJUNCT2(SPEC_ALL BESSEL_DJ1_SIGNS)) THEN
      ASM_REWRITE_TAC[ODD_ADD; ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. sum(0..n) e) --->
     bessel_dj1 x - sum(0..1) (bessel_dj1_term x)) sequentially`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_SERIES_FROM] THEN EXPAND_TAC "e" THEN
    REWRITE_TAC[REAL_SUMS_REINDEX] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [`bessel_dj1_term x`; `bessel_dj1 x`; `0`; `2`]
                  REAL_SUMS_OFFSET) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[BESSEL_DJ1_SUMS];
    ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM NOT_EVEN]) THENL
   [MATCH_MP_TAC(REAL_ARITH `b <= l - a ==> a + b <= l`) THEN
    MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND);
    MATCH_MP_TAC(REAL_ARITH `l - a <= b ==> l <= a + b`) THEN
    MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND)] THEN
  EXISTS_TAC `\n. sum(0..n) (e:num->real)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `M:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`e:num->real`; `0`; `M:num`; `n:num`] SUM_COMBINE_R) THEN
  ASM_REWRITE_TAC[LE_0] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`M + 1`; `n:num`] o
                check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[EVEN_ADD; GSYM NOT_EVEN; ARITH] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Headline: J_1' changes sign on [1.8411, 1.8412].                          *)
(* ------------------------------------------------------------------------- *)

let BESSEL_EVAL_TAC =
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
  REWRITE_TAC[bessel_dj1_term] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV NUM_FACT_CONV) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV;;

let BESSEL_DJ1_POS_AT_18411 = prove
 (`&0 < bessel_dj1(&18411 / &10000)`,
  MP_TAC(SPECL [`&18411 / &10000`; `3`] BESSEL_DJ1_PARTIAL_BOUNDS) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[ARITH] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < a ==> a <= b ==> &0 < b`) THEN
  BESSEL_EVAL_TAC);;

let BESSEL_DJ1_NEG_AT_18412 = prove
 (`bessel_dj1(&18412 / &10000) < &0`,
  MP_TAC(SPECL [`&18412 / &10000`; `4`] BESSEL_DJ1_PARTIAL_BOUNDS) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[ARITH] THEN
  MATCH_MP_TAC(REAL_ARITH `a < &0 ==> b <= a ==> b < &0`) THEN
  BESSEL_EVAL_TAC);;

(* ------------------------------------------------------------------------- *)
(* New in this leaf: bessel_dj1 is continuous on [1,2] (uniform limit of its  *)
(* partial sums, Weierstrass M-test), hence it has a zero in the bracket.     *)
(* ------------------------------------------------------------------------- *)

let BESSEL_DJ1_DEN_GE_2 = prove
 (`!k. 1 <= k
       ==> &2 <= ((&2 * &k + &1) * (&k + &1) * (&k + &2)) / (&2 * &k + &3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 * &k + &3` ASSUME_TAC THENL
   [MP_TAC(SPEC `k:num` REAL_POS) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `&1 <= (&k:real)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&k:real) * (&k - &1) /\ &0 <= (&k:real) * &k * &k`
  MP_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let BESSEL_DJ1_ABS = prove
 (`!x k. abs(bessel_dj1_term x k) =
         (&2 * &k + &1) * (x pow 2 / &4) pow k /
         (&2 * &(FACT k) * &(FACT(SUC k)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bessel_dj1_term] THEN
  ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
  REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NEG; REAL_ABS_NUM; REAL_POW_ONE;
              REAL_MUL_LID; REAL_ABS_REFL; BESSEL_DJ1_MAGNITUDE_POS]);;

let BESSEL_DJ1_TERM_BOUND = prove
 (`!x k. abs x <= &2
         ==> abs(bessel_dj1_term x k) <= abs(bessel_dj1_term (&2) k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BESSEL_DJ1_ABS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MP_TAC(SPEC `k:num` REAL_POS) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * &(FACT k) * &(FACT(SUC k))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_MUL] THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT; ARITH];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  SUBGOAL_THEN `abs x pow 2 <= &2 pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let BESSEL_DJ1_MAJORANT_SUMMABLE = prove
 (`real_summable (from 0) (\k. abs(bessel_dj1_term (&2) k))`,
  MATCH_MP_TAC RATIO_SUMMABLE THEN
  EXISTS_TAC `\k. abs(--((&2:real) pow 2 / &4) /
     (((&2 * &k + &1) * (&k + &1) * (&k + &2)) / (&2 * &k + &3)))` THEN
  EXISTS_TAC `1` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[BESSEL_DJ1_STEP; REAL_ABS_MUL; REAL_ABS_ABS] THEN
  MATCH_MP_TAC RATIO_BOUND THEN ASM_SIMP_TAC[BESSEL_DJ1_DEN_GE_2] THEN
  REAL_ARITH_TAC);;

(* Uniform limits of continuous real functions are continuous.              *)
let REAL_CONTINUOUS_ON_UNIFORM_LIMIT_SEQ = prove
 (`!f:num->real->real g s.
     (!n. (f n) real_continuous_on s) /\
     (!e. &0 < e ==> ?N. !n x. N <= n /\ x IN s ==> abs(f n x - g x) < e)
     ==> g real_continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON] THEN
  MATCH_MP_TAC(ISPEC `sequentially` CONTINUOUS_UNIFORM_LIMIT) THEN
  EXISTS_TAC `\n:num. lift o (f:num->real->real) n o drop` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY;
              FORALL_IN_IMAGE; o_THM; LIFT_DROP; GSYM LIFT_SUB; NORM_LIFT] THEN
  ASM_REWRITE_TAC[GSYM REAL_CONTINUOUS_ON] THEN ASM_MESON_TAC[]);;

let BESSEL_DJ1_TERM_CONTINUOUS = prove
 (`!k s. (\x. bessel_dj1_term x k) real_continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bessel_dj1_term; real_div] THEN
  REPEAT((MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL ORELSE
          MATCH_MP_TAC REAL_CONTINUOUS_ON_RMUL ORELSE
          MATCH_MP_TAC REAL_CONTINUOUS_ON_POW)) THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_ID]);;

let NEGCTL_BESSEL_J1_TERM_DERIV_IS_J0 = prove
 (`!x k. ((\x. bessel_j1_term x k) has_real_derivative bessel_j0_term x k)
         (atreal x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bessel_j1_term; bessel_j0_term] THEN
  REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN
  STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THENL
   [REWRITE_TAC[real_pow; FACT; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[ARITH_RULE `SUC n - 1 = n`; real_pow; FACT;
                GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_SUC] THEN
    MP_TAC(SPEC `n:num` FACT_NZ) THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    MP_TAC(SPEC `n:num` REAL_POS) THEN
    SPEC_TAC(`&(FACT n)`,`f:real`) THEN SPEC_TAC(`&n`,`m:real`) THEN
    SPEC_TAC(`(--(&1)) pow n`,`s:real`) THEN
    SPEC_TAC(`(x pow 2 / &4) pow n`,`p:real`) THEN
    CONV_TAC REAL_FIELD]);;
