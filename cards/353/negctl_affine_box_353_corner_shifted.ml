(* ========================================================================= *)
(* NEGATIVE CONTROL written for openai-math-hol-cards (2026-10-07).         *)
(* Family 353: the stationary corner claimed at (9/2, 7/2, 34/7).            *)
(* False: at d = 34/7 the B- and D-components are nonzero.                   *)
(* It reuses the leaf's tactic on a FALSE variant. Expected: FAILED.      *)
(* ========================================================================= *)

let NEGCTL_AB353_CORNER_D_34_7 = prove
 (`let a = &9 / &2 and b = &7 / &2 and d = &34 / &7 in
   a * (&1 + b - a) = &0 /\
   b * (&9 + a + (&12 / &11) * b * d - &9 * b) = &0 /\
   (&11 - d) * a - &8 * d + b * d * (&1 - d / &11) = &0`,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[]);;
