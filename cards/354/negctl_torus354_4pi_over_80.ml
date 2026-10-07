(* ========================================================================= *)
(* NEGATIVE CONTROL for torus354_pi.ml (family 354). Must FAIL.               *)
(* Same lemmas, then the claim that ball and tube tie at V = 4 pi/80 instead  *)
(* of 4 pi/81, attempted by reducing it to the main switch theorem.           *)
(* ========================================================================= *)

let PI_BOUNDS_4DIGITS = prove
 (`&31415 / &10000 < pi /\ pi < &31416 / &10000`,
  MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

(* Generic lemmas: PI any positive constant (as in the light scout run).    *)
(* Free variables in subgoal terms carry explicit :real annotations, since  *)
(* heavy also overloads pow and & for complex numbers.                      *)
let T354_POW_LE_EQ = prove
 (`!n x y. ~(n = 0) /\ &0 <= x /\ &0 <= y ==> (x pow n <= y pow n <=> x <= y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LE] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]]);;

let T354_BALL_TUBE_SWITCH = prove
 (`!PI V b t.
     &0 < PI /\ &0 < V /\ &0 <= b /\ &0 <= t /\
     b pow 3 = &36 * PI * V pow 2 /\ t pow 2 = &4 * PI * V
     ==> (b <= t <=> V <= &4 * PI / &81)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`6`; `b:real`; `t:real`] T354_POW_LE_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `(b:real) pow 6 = (b pow 3) pow 2 /\ (t:real) pow 6 = (t pow 2) pow 3`
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

let T354_TUBE_SLAB_SWITCH = prove
 (`!PI V t.
     &0 < PI /\ &0 < V /\ &0 <= t /\ t pow 2 = &4 * PI * V
     ==> (t <= &2 <=> V <= &1 / PI)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2`; `t:real`; `&2`] T354_POW_LE_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

(* Ball area b = 4 pi r^2 satisfies b^3 = 36 pi V^2; tube area t = 2 pi s   *)
(* satisfies t^2 = 4 pi V. These are the paper's (36 pi)^(1/3) V^(2/3) and  *)
(* 2 sqrt(pi V).                                                             *)
let T354_BALL_AREA = prove
 (`!V r. &4 / &3 * pi * r pow 3 = V
         ==> (&4 * pi * r pow 2) pow 3 = &36 * pi * V pow 2`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC REAL_RING);;

let T354_TUBE_AREA = prove
 (`!V s. pi * s pow 2 = V ==> (&2 * pi * s) pow 2 = &4 * pi * V`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC REAL_RING);;

(* Headline.                                                                *)
let T354_PI_SWITCHES = prove
 (`!V r s. &0 < V /\ &0 < r /\ &0 < s /\
           &4 / &3 * pi * r pow 3 = V /\ pi * s pow 2 = V
           ==> (&4 * pi * r pow 2 <= &2 * pi * s <=> V <= &4 * pi / &81) /\
               (&2 * pi * s <= &2 <=> V <= &1 / pi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`V:real`; `r:real`] T354_BALL_AREA) THEN
  MP_TAC(SPECL [`V:real`; `s:real`] T354_TUBE_AREA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC T354_BALL_TUBE_SWITCH;
    MATCH_MP_TAC T354_TUBE_SLAB_SWITCH] THEN
  ASM_REWRITE_TAC[PI_POS] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; PI_POS_LE; REAL_LE_MUL; REAL_POW_LE;
               REAL_POS]);;

let NEGCTL_T354_PI_SWITCH_AT_4PI_OVER_80 = prove
 (`!V r s. &0 < V /\ &0 < r /\ &0 < s /\
           &4 / &3 * pi * r pow 3 = V /\ pi * s pow 2 = V
           ==> (&4 * pi * r pow 2 <= &2 * pi * s <=> V <= &4 * pi / &80)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`V:real`; `r:real`; `s:real`] T354_PI_SWITCHES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  MP_TAC PI_BOUNDS_4DIGITS THEN ASM_REAL_ARITH_TAC);;
