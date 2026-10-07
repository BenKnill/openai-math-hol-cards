(* ========================================================================= *)
(* NEGATIVE CONTROL written for openai-math-hol-cards (2026-10-07).         *)
(* Family 196: the first bound claimed below 99/100 instead of 149/150.      *)
(* The value 500731261911/504183783481 = 0.99315... exceeds 99/100.          *)
(* It reuses the leaf's tactic on a FALSE variant. Expected: FAILED.      *)
(* ========================================================================= *)

let NEGCTL_K196_FIRST_BOUND_BELOW_99_100 = prove
 (`let q = &128 and v = &16513 and p = &129 / &16513 in
   q / (q + &1) + &3 * p pow 2 + &12 / (q + &1) pow 2 =
     &500731261911 / &504183783481 /\
   &500731261911 / &504183783481 < &99 / &100 /\
   (&2 + v * p pow 2 + &12 * p pow 2) / &5 = &820350863 / &1363395845 /\
   &820350863 / &1363395845 < &149 / &150`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[]);;
