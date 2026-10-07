(* ========================================================================= *)
(* Family 188 of the OpenAI math release: "The Sharp Terminal Leave in       *)
(* Random Triangle Removal" (September 25, 2026). The film's one-line aha:   *)
(* Spencer's scalar branching law dq/dt = -D q^3 and the constant 1/(2 sqrt 2)*)
(* Profile: heavy (real derivatives, sqrt, real sequence limits).            *)
(*                                                                            *)
(* Checked here (no new definitions):                                         *)
(*   TR188_SPENCER_LAW  for every D >= 0, q(t) = (1 + 2 D t)^(-1/2)           *)
(*     satisfies q(0) = 1 and, at every t >= 0, q'(t) = -D q(t)^3.            *)
(*     (Two-sided real derivative, HOL's has_real_derivative ... (atreal t).) *)
(*   TR188_LEAVE_CONSTANT                                                     *)
(*     (n^2/2) (1 + 2n)^(-1/2) / n^(3/2)  -->  1/(2 sqrt 2)  as n -> infinity *)
(*     with n^(3/2) written as n sqrt(n). This is the heuristic's arithmetic: *)
(*     about n^2/2 edges, each surviving with probability q(1), D = n.        *)
(*   TR188_SPENCER_CARD  both of the above in one theorem.                    *)
(*                                                                            *)
(* NOT checked here: anything about the random process. That q is the         *)
(* survival probability of an edge is Spencer's heuristic (it treats the      *)
(* partner edges as independent); the paper's whole job is to make that       *)
(* rigorous, and its theorem (terminal edge count / n^(3/2) -> 1/(2 sqrt 2)   *)
(* in L^2) is Lean-formalized in the release (lean/docs/188.md), not here.    *)
(* Also not checked: uniqueness of the ODE solution.                          *)
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

let TR188_SPENCER_LAW = prove
 (`!D. &0 <= D
       ==> inv(sqrt(&1 + &2 * D * &0)) = &1 /\
           !x. &0 <= x
               ==> ((\t. inv(sqrt(&1 + &2 * D * t))) has_real_derivative
                    (--D * inv(sqrt(&1 + &2 * D * x)) pow 3)) (atreal x)`,
  SIMP_TAC[TR188_Q_AT_0; TR188_SURVIVAL_ODE]);;

(* The algebra behind the limit: with a = sqrt n, b = sqrt(1 + 2n) and      *)
(* c = sqrt(2 + 1/n), a b = n c, so the expression equals 1/(2 c).           *)
let TR188_ALG = prove
 (`!(n:real) (a:real) (b:real) (c:real).
        ~(n = &0) /\ ~(a = &0) /\ ~(b = &0) /\ ~(c = &0) /\ a * b = n * c
        ==> ((n pow 2 / &2) * inv b) / (n * a) = inv(&2 * c)`,
  CONV_TAC REAL_FIELD);;

let TR188_SQRT_PRODUCT = prove
 (`!n. 1 <= n
       ==> sqrt(&n) * sqrt(&1 + &2 * &n) = &n * sqrt(&2 + inv(&n))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 + inv(&n)` ASSUME_TAC THENL
   [MP_TAC(SPEC `&n` REAL_LE_INV) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN
  REWRITE_TAC[ARITH_EQ] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_POS;
               REAL_ARITH `&0 < x ==> &0 <= &1 + &2 * x`] THEN
  SUBGOAL_THEN `~(&n = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let TR188_LEAVE_CONSTANT = prove
 (`((\n. ((&n pow 2 / &2) * inv(sqrt(&1 + &2 * &n))) / (&n * sqrt(&n)))
    ---> inv(&2 * sqrt(&2))) sequentially`,
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. inv(&2 * sqrt(&2 + inv(&n)))` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC TR188_ALG THEN
    ASM_SIMP_TAC[TR188_SQRT_PRODUCT] THEN
    SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv(&n)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    TRY(MATCH_MP_TAC SQRT_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_INV THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_ENTIRE; SQRT_EQ_0] THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REALLIM_LMUL THEN
  MATCH_MP_TAC REALLIM_REAL_CONTINUOUS_FUNCTION THEN
  REWRITE_TAC[REAL_CONTINUOUS_AT_SQRT] THEN
  SUBGOAL_THEN `((\n. &2 + inv(&n)) ---> &2 + &0) sequentially` MP_TAC THENL
   [MATCH_MP_TAC REALLIM_ADD THEN
    REWRITE_TAC[REALLIM_CONST; REALLIM_1_OVER_N];
    REWRITE_TAC[REAL_ADD_RID]]);;

(* The card's headline, as one theorem.                                     *)
let TR188_SPENCER_CARD = prove
 (`(!D. &0 <= D
        ==> inv(sqrt(&1 + &2 * D * &0)) = &1 /\
            !x. &0 <= x
                ==> ((\t. inv(sqrt(&1 + &2 * D * t))) has_real_derivative
                     (--D * inv(sqrt(&1 + &2 * D * x)) pow 3)) (atreal x)) /\
   ((\n. ((&n pow 2 / &2) * inv(sqrt(&1 + &2 * &n))) / (&n * sqrt(&n)))
    ---> inv(&2 * sqrt(&2))) sequentially`,
  REWRITE_TAC[TR188_SPENCER_LAW; TR188_LEAVE_CONSTANT]);;
