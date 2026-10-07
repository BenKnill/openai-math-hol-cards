(* ========================================================================= *)
(* Family 353, paper                                                         *)
(*   Smooth-Nonquadratic-Affine-Maximal-Graph-in-Dimension-Ten-October-5-2026*)
(*   (build/source/main.tex, Section 4, Lemmas 4.1 and 4.2).                *)
(*                                                                           *)
(* HOL Light check of the finite algebraic kernel of the invariant box       *)
(*   B = [0,9/2] x [0,7/2] x [0,33/7]                                        *)
(* for the autonomous system (m = 9, k = 11, gamma = 12/11)                  *)
(*   A' = A (1 + B - A)                                                      *)
(*   B' = B (9 + A + (12/11) B D - 9 B)                                      *)
(*   D' = (11 - D) A - 8 D + B D (1 - D/11).                                 *)
(*                                                                           *)
(* Covered: the D-equation follows from the paper's C-equation with          *)
(* D = C/B (general m, k, gamma); the upper corner (9/2,7/2,33/7) is a       *)
(* stationary point; the cross-partial signs on the box; the sign of each    *)
(* component on every face of the box.                                       *)
(* NOT covered: the ODE derivation of the A, B, C equations from the radial  *)
(* system, the invariance argument itself (projection + Gronwall), the local *)
(* solution at r = 0, Proposition 2.1 (reduction of the fourth-order PDE),   *)
(* and smoothness/positivity of the resulting u on R^10.                     *)
(* ========================================================================= *)

(* Lemma 4.1: from the C-equation to the D-equation, D = C / B.              *)
let AB353_D_EQUATION = prove
 (`!m k g a b c ad bd cd.
     ~(b = &0) /\
     ad = a * (&1 + b - a) /\
     bd = b * (m + a + g * c - m * b) /\
     cd = c * (&1 + c - (m - &1) * b) + k * a * b
     ==> (cd * b - c * bd) / b pow 2 =
         (k - c / b) * a - (m - &1) * (c / b) +
         b * (c / b) * (&1 + (&1 - g) * (c / b))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(b = &0)` THEN CONV_TAC REAL_FIELD);;

(* The vector field at m = 9, k = 11, gamma = 12/11 vanishes at the corner.  *)
let AB353_CORNER_STATIONARY = prove
 (`let a = &9 / &2 and b = &7 / &2 and d = &33 / &7 in
   a * (&1 + b - a) = &0 /\
   b * (&9 + a + (&12 / &11) * b * d - &9 * b) = &0 /\
   (&11 - d) * a - &8 * d + b * d * (&1 - d / &11) = &0`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[]);;

(* Cross partial derivatives are nonnegative on the box (the paper lists     *)
(* them; here we check the listed values are >= 0 on B).                     *)
let AB353_CROSS_PARTIALS_NONNEG = prove
 (`!a b d.
     &0 <= a /\ a <= &9 / &2 /\ &0 <= b /\ b <= &7 / &2 /\
     &0 <= d /\ d <= &33 / &7
     ==> &0 <= a /\ &0 <= b /\ &0 <= (&12 / &11) * b pow 2 /\
         &0 <= &11 - d /\ &0 <= d * (&1 - d / &11)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
  TRY ASM_REAL_ARITH_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
  TRY(REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC) THEN ASM_REAL_ARITH_TAC);;

(* Face conditions: on each upper face the outward component is <= 0, on     *)
(* each lower face the inward component is >= 0.                            *)
let AB353_FACE_SIGNS = prove
 (`!a b d.
     &0 <= a /\ a <= &9 / &2 /\ &0 <= b /\ b <= &7 / &2 /\
     &0 <= d /\ d <= &33 / &7
     ==> (a = &9 / &2 ==> a * (&1 + b - a) <= &0) /\
         (b = &7 / &2
          ==> b * (&9 + a + (&12 / &11) * b * d - &9 * b) <= &0) /\
         (d = &33 / &7
          ==> (&11 - d) * a - &8 * d + b * d * (&1 - d / &11) <= &0) /\
         (a = &0 ==> a * (&1 + b - a) = &0) /\
         (b = &0 ==> b * (&9 + a + (&12 / &11) * b * d - &9 * b) = &0) /\
         (d = &0
          ==> &0 <= (&11 - d) * a - &8 * d + b * d * (&1 - d / &11))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
  DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC);;
