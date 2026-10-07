(* Split from onscreen_light_batch.ml (math-drop lane, sha256 1d61b1ec6d77),  *)
(* lines 25-95, verbatim below the batch header.                         *)

(* ========================================================================= *)
(* Small on-screen certificates forwarded by the video scouts (2026-10-07).  *)
(* Profile: light (core HOL Light + calc_rat + ringtheory; no pi, no sin).   *)
(* Each block states exactly what it covers.                                 *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Family 354 (isoperimetric profile of the cubic flat 3-torus), paper       *)
(* The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-...-24-2026.  *)
(* The light profile has no pi, so PI below is ANY positive real; the        *)
(* statements hold for every such constant, in particular for pi.            *)
(* Candidate areas at volume V: ball b with b^3 = 36 PI V^2,                 *)
(* tube (around a unit closed geodesic) t with t^2 = 4 PI V, slab 2.         *)
(* Covers: where the three candidate curves cross, and the radii there.      *)
(* Does NOT cover: that these candidates are the minimizers (the theorem).   *)
(* ------------------------------------------------------------------------- *)

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

(* The radii at the two switch volumes: ball radius 1/3 and tube radius 2/9 *)
(* at V = 4 PI/81, both with area 4 PI/9; tube radius 1/PI at V = 1/PI with *)
(* area 2 = slab area. With 3 < PI (true of pi) every radius is < 1/2, so   *)
(* each shape fits in the unit cube torus.                                  *)
let T354_SWITCH_RADII = prove
 (`!PI. &3 < PI
        ==> (&4 / &3 * PI * (&1 / &3) pow 3 = &4 * PI / &81 /\
             &4 * PI * (&1 / &3) pow 2 = &4 * PI / &9 /\
             PI * (&2 / &9) pow 2 = &4 * PI / &81 /\
             &2 * PI * (&2 / &9) = &4 * PI / &9) /\
            (PI * (&1 / PI) pow 2 = &1 / PI /\
             &2 * PI * (&1 / PI) = &2) /\
            &1 / &3 < &1 / &2 /\ &2 / &9 < &1 / &2 /\ &1 / PI < &1 / &2`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(PI = &0) /\ &0 < PI` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC) THEN
  TRY(UNDISCH_TAC `~(PI = &0)` THEN CONV_TAC REAL_FIELD THEN NO_TAC) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;
