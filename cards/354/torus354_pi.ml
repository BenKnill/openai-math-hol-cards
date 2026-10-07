(* ========================================================================= *)
(* Family 354 of the OpenAI math release: "The Isoperimetric Conjecture for  *)
(* the Cubic Flat Three-Torus" (September 24, 2026), Theorem 1.1: in R^3/Z^3 *)
(* the least perimeter for volume v <= 1/2 is                                 *)
(*   min{ (36 pi)^(1/3) v^(2/3),  2 sqrt(pi v),  2 }   (ball, tube, slab).    *)
(* Profile: heavy, so that pi below is HOL Light's real pi. (The 00:53 scout  *)
(* run on light proved the same switches for an arbitrary positive constant.) *)
(*                                                                            *)
(* The three candidates at volume V, described by their radii:               *)
(*   ball of radius r:  V = (4/3) pi r^3,  area 4 pi r^2;                     *)
(*   tube of radius s around a unit closed geodesic:  V = pi s^2,             *)
(*     area 2 pi s;                                                           *)
(*   slab (two parallel unit squares):  area 2.                               *)
(* Checked here:                                                              *)
(*   T354_PI_SWITCHES  for every V > 0: ball area <= tube area iff            *)
(*     V <= 4 pi/81, and tube area <= 2 iff V <= 1/pi.                        *)
(*   T354_PI_SWITCH_VALUES  at V = 4 pi/81 the ball radius is exactly 1/3 and *)
(*     the tube radius exactly 2/9, both areas 4 pi/9; at V = 1/pi the tube   *)
(*     radius is 1/pi and its area is 2; 4 pi/81 < 1/pi < 1/2;                *)
(*     0.1551 < 4 pi/81 < 0.1552 and 0.3183 < 1/pi < 0.3184; every radius     *)
(*     is < 1/2, so no shape touches its own periodic copy.                   *)
(*   T354_PI_BALL_LOSES_AT_SLAB_SWITCH  at V = 1/pi a ball has area > 2.      *)
(* The only facts about pi used are 3 < pi < 4 (from HOL Light's             *)
(* PI_APPROX_32) and, for the decimals, its first four digits.                *)
(*                                                                            *)
(* NOT checked here: that ball, tube and slab are the minimizers, i.e. the    *)
(* theorem itself (Lean-formalized in the release, lean/docs/354.md; not      *)
(* re-run by us), nor the existence of minimizers.                            *)
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

let T354_INV_PI_FACTS = prove
 (`&4 * pi / &81 < &1 / pi /\ &1 / pi < &1 / &2 /\
   &3183 / &10000 < &1 / pi /\ &1 / pi < &3184 / &10000`,
  MP_TAC PI_BOUNDS_4DIGITS THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < pi` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SPECL [`&4 * pi / &81`; `&1`; `pi`] REAL_LT_RDIV_EQ] THEN
    SUBGOAL_THEN `&0 < (&4 - pi) * pi` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[SPECL [`&1`; `&1 / &2`; `pi`] REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[SPECL [`&3183 / &10000`; `&1`; `pi`] REAL_LT_RDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[SPECL [`&1`; `&3184 / &10000`; `pi`] REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC]);;

let T354_PI_SWITCH_VALUES = prove
 (`(&4 / &3 * pi * (&1 / &3) pow 3 = &4 * pi / &81 /\
    pi * (&2 / &9) pow 2 = &4 * pi / &81 /\
    &4 * pi * (&1 / &3) pow 2 = &4 * pi / &9 /\
    &2 * pi * (&2 / &9) = &4 * pi / &9) /\
   (pi * (&1 / pi) pow 2 = &1 / pi /\
    &2 * pi * (&1 / pi) = &2) /\
   &4 * pi / &81 < &1 / pi /\ &1 / pi < &1 / &2 /\
   &1551 / &10000 < &4 * pi / &81 /\ &4 * pi / &81 < &1552 / &10000 /\
   &3183 / &10000 < &1 / pi /\ &1 / pi < &3184 / &10000 /\
   &1 / &3 < &1 / &2 /\ &2 / &9 < &1 / &2`,
  REWRITE_TAC[T354_INV_PI_FACTS] THEN
  MP_TAC PI_BOUNDS_4DIGITS THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(pi = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC) THEN
  TRY(UNDISCH_TAC `~(pi = &0)` THEN CONV_TAC REAL_FIELD THEN NO_TAC) THEN
  ASM_REAL_ARITH_TAC);;

(* At the tube/slab switch V = 1/pi a ball would need area > 2.             *)
let T354_PI_BALL_LOSES_AT_SLAB_SWITCH = prove
 (`!r. &0 < r /\ &4 / &3 * pi * r pow 3 = &1 / pi ==> &2 < &4 * pi * r pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&1 / pi`; `r:real`] T354_BALL_AREA) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`3`; `&4 * pi * r pow 2`; `&2`] T354_POW_LE_EQ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[PI_POS_LE; REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC PI_BOUNDS_4DIGITS THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < pi` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&36 * pi * (&1 / pi) pow 2 = &36 / pi` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < pi` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REAL_ARITH_TAC);;
