(* Split from onscreen_light_batch.ml (math-drop lane, sha256 1d61b1ec6d77),  *)
(* lines 130-145, verbatim below the batch header.                         *)

(* ========================================================================= *)
(* Small on-screen certificates forwarded by the video scouts (2026-10-07).  *)
(* Profile: light (core HOL Light + calc_rat + ringtheory; no pi, no sin).   *)
(* Each block states exactly what it covers.                                 *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Family 325 (complete Crouzeix), the sharpness arithmetic in real form:    *)
(* if x^2 + y^2 = 1 then |2 x y| <= 1. With x = |a|, y = |b| this is the     *)
(* paper's |2 conj(a) b| <= 1 when |a|^2 + |b|^2 = 1; the modulus identity   *)
(* |conj a| = |a| needs complex numbers, which light does not load.          *)
(* ------------------------------------------------------------------------- *)

let C325_TWO_XY = prove
 (`!x y. x pow 2 + y pow 2 = &1 ==> abs(&2 * x * y) <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_BOUNDS] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `&0 <= (x + y) pow 2 ==> --(x pow 2 + y pow 2) <= &2 * x * y`);
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= (x - y) pow 2 ==> &2 * x * y <= x pow 2 + y pow 2`)] THEN
  REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]);;
