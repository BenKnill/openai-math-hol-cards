(* Split from onscreen_light_batch.ml (math-drop lane, sha256 1d61b1ec6d77),  *)
(* lines 97-128, verbatim below the batch header.                         *)

(* ========================================================================= *)
(* Small on-screen certificates forwarded by the video scouts (2026-10-07).  *)
(* Profile: light (core HOL Light + calc_rat + ringtheory; no pi, no sin).   *)
(* Each block states exactly what it covers.                                 *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Family 028 (Gaussian moat), the periodicity step: a finite nonempty set   *)
(* of points in the plane (here real pairs; Z^2 is a special case) is not    *)
(* invariant under any nonzero translation.                                  *)
(* ------------------------------------------------------------------------- *)

let M028_FINITE_NOT_TRANSLATION_INVARIANT = prove
 (`!s:(real#real)->bool a b.
     FINITE s /\ ~(s = {}) /\
     IMAGE (\z. (FST z + a, SND z + b)) s = s
     ==> a = &0 /\ b = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(&(CARD(s:(real#real)->bool)) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_MESON_TAC[CARD_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN s /\ y IN s /\
          (\z:real#real. (FST z + a, SND z + b)) x =
          (\z:real#real. (FST z + a, SND z + b)) y ==> x = y`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN
    SIMP_TAC[REAL_EQ_ADD_RCANCEL]; ALL_TAC] THEN
  FIRST_ASSUM(fun inj ->
    MP_TAC(MATCH_MP (ISPECL [`\z:real#real. (FST z + a, SND z + b)`;
                             `FST:real#real->real`;
                             `s:(real#real)->bool`] SUM_IMAGE) inj) THEN
    MP_TAC(MATCH_MP (ISPECL [`\z:real#real. (FST z + a, SND z + b)`;
                             `SND:real#real->real`;
                             `s:(real#real)->bool`] SUM_IMAGE) inj)) THEN
  ASM_REWRITE_TAC[o_DEF] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_CONST; ETA_AX] THEN
  REWRITE_TAC[REAL_ARITH `x = x + y <=> y = &0`; REAL_ENTIRE] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;
