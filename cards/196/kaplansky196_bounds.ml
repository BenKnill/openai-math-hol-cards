(* Split from onscreen_light_batch.ml (math-drop lane, sha256 1d61b1ec6d77),  *)
(* lines 7-23, verbatim below the batch header.                         *)

(* ========================================================================= *)
(* Small on-screen certificates forwarded by the video scouts (2026-10-07).  *)
(* Profile: light (core HOL Light + calc_rat + ringtheory; no pi, no sin).   *)
(* Each block states exactly what it covers.                                 *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Family 196 (Kaplansky zero divisors), paper                               *)
(* A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026,        *)
(* build/sections/types.tex lines 81-91: with q = 128, v = 16513,            *)
(* p = 129/16513, the two exact values and the two "< 149/150" bounds.       *)
(* Covers only the arithmetic; the bounds on (Mf)(t) are the paper's.        *)
(* ------------------------------------------------------------------------- *)

let K196_RATIONAL_BOUNDS = prove
 (`let q = &128 and v = &16513 and p = &129 / &16513 in
   q / (q + &1) + &3 * p pow 2 + &12 / (q + &1) pow 2 =
     &500731261911 / &504183783481 /\
   &500731261911 / &504183783481 < &149 / &150 /\
   (&2 + v * p pow 2 + &12 * p pow 2) / &5 = &820350863 / &1363395845 /\
   &820350863 / &1363395845 < &149 / &150`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[]);;
