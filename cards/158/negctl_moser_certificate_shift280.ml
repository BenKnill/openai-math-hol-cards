(* ========================================================================= *)
(* Family 158 of the OpenAI math release (Sept 2026):                         *)
(*   "The Euclidean plane is not five-colorable", angular.tex,                *)
(*   Lemma (Seven-point certificate) and the Moser-graph facts used in        *)
(*   Proposition (interface cycle cannot have length three).                 *)
(*                                                                            *)
(* Checked here: the seven placed Moser vertices z_g lie strictly inside the  *)
(* polynomial three-label region (0 < l < 4 and P < P'), the eleven placed    *)
(* edges have length exactly one, and no colouring of the seven placed points *)
(* with three labels avoids a monochromatic unit pair.                        *)
(*                                                                            *)
(* NOT checked here: Lemma (Polynomial three-label region), i.e. that this    *)
(* region really is restricted to three labels, nor anything else in the      *)
(* paper. The main theorem has its own Lean formalization (lean/docs/158.md). *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Radicals.                                                                 *)
(* ------------------------------------------------------------------------- *)

let SQRT_3_POW_2 = prove
 (`sqrt(&3) pow 2 = &3`,
  SIMP_TAC[SQRT_POW_2; REAL_POS]);;

let SQRT_11_POW_2 = prove
 (`sqrt(&11) pow 2 = &11`,
  SIMP_TAC[SQRT_POW_2; REAL_POS]);;

let SQRT_33_EQ = prove
 (`sqrt(&33) = sqrt(&3) * sqrt(&11)`,
  SIMP_TAC[GSYM SQRT_MUL; REAL_POS] THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let SQRT_BOUND_TAC =
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC REAL_LT_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV];;

let SQRT_3_BOUNDS = prove
 (`&1732050807568 / &1000000000000 < sqrt(&3) /\
   sqrt(&3) < &1732050807569 / &1000000000000`,
  SQRT_BOUND_TAC);;

let SQRT_11_BOUNDS = prove
 (`&3316624790355 / &1000000000000 < sqrt(&11) /\
   sqrt(&11) < &3316624790356 / &1000000000000`,
  SQRT_BOUND_TAC);;

let SQRT_33_BOUNDS = prove
 (`&5744562646538 / &1000000000000 < sqrt(&3) * sqrt(&11) /\
   sqrt(&3) * sqrt(&11) < &5744562646539 / &1000000000000`,
  REWRITE_TAC[GSYM SQRT_33_EQ] THEN SQRT_BOUND_TAC);;

(* ------------------------------------------------------------------------- *)
(* The placement z_g = (35 + 12i)/37 (g + (-290 + 149i)/250) and the region.  *)
(* ------------------------------------------------------------------------- *)

let moser_xi = new_definition
 `moser_xi (gx:real) (gy:real) =
    (&35 * (gx - &280 / &250) - &12 * (gy + &149 / &250)) / &37`;;

let moser_ups = new_definition
 `moser_ups (gx:real) (gy:real) =
    (&12 * (gx - &280 / &250) + &35 * (gy + &149 / &250)) / &37`;;

let three_label_region = new_definition
 `three_label_region (xi:real) (ups:real) <=>
    &0 < xi pow 2 + ups pow 2 /\
    xi pow 2 + ups pow 2 < &4 /\
    ups pow 2 * (&3 * xi pow 2 - ups pow 2) pow 2 <
    (xi pow 2 + ups pow 2) pow 3 * (&1 - (xi pow 2 + ups pow 2) / &4) *
    ((xi pow 2 + ups pow 2) - &1) pow 2`;;

(* ------------------------------------------------------------------------- *)
(* Q(sqrt 3, sqrt 11) sign check: REAL_RING proves b - a = nf from           *)
(* s^2 = 3, t^2 = 11, then linear arithmetic bounds nf from the radicals.    *)
(* ------------------------------------------------------------------------- *)

let QST_LT_TAC (nf:term) : tactic =
  fun (asl,w as gl) ->
    let a,b = dest_binop `(<):real->real->bool` w in
    let eq = mk_eq(mk_binop `(-):real->real->real` b a, nf) in
    let ith = REAL_RING
      (mk_imp(`s pow 2 = &3 /\ t pow 2 = &11`, eq)) in
    let th = MP ith (CONJ (ASSUME `s pow 2 = &3`) (ASSUME `t pow 2 = &11`)) in
    (ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN REWRITE_TAC[th] THEN
     ASM_REAL_ARITH_TAC) gl;;

let QST_SETUP_TAC =
  REWRITE_TAC[three_label_region; moser_xi; moser_ups; SQRT_33_EQ] THEN
  MP_TAC(CONJ SQRT_3_POW_2 (CONJ SQRT_11_POW_2
    (CONJ SQRT_3_BOUNDS (CONJ SQRT_11_BOUNDS SQRT_33_BOUNDS)))) THEN
  SPEC_TAC(`sqrt(&11)`,`t:real`) THEN SPEC_TAC(`sqrt(&3)`,`s:real`) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS);;

let QST_REGION_TAC nl n4l ngap =
  QST_SETUP_TAC THEN REPEAT CONJ_TAC THENL
   [QST_LT_TAC nl; QST_LT_TAC n4l; QST_LT_TAC ngap];;

(* ------------------------------------------------------------------------- *)
(* Lemma (Seven-point certificate): every placed vertex is in the region.    *)
(* ------------------------------------------------------------------------- *)

let MOSER_REGION_O = prove
 (`three_label_region (moser_xi (&0) (&0))
                      (moser_ups (&0) (&0))`,
  QST_REGION_TAC
   `(&100601 / &62500) + (&0) * s + (&0) * t + (&0) * (s * t)`
   `(&149399 / &62500) + (&0) * s + (&0) * t + (&0) * (s * t)`
   `(&30489581973885721512805660606907326191 / &611716844797134399414062500000000000000) + (&0) * s + (&0) * t + (&0) * (s * t)`);;

let MOSER_REGION_A = prove
 (`three_label_region (moser_xi (sqrt(&3) / &2) (&1 / &2))
                      (moser_ups (sqrt(&3) / &2) (&1 / &2))`,
  QST_REGION_TAC
   `(&200351 / &62500) + --(&28 / &25) * s + (&0) * t + (&0) * (s * t)`
   `(&49649 / &62500) + (&28 / &25) * s + (&0) * t + (&0) * (s * t)`
   `--(&215403234823563111419843025358091991397809 / &611716844797134399414062500000000000000) + (&6219503822406518802187438486017247839 / &30585842239856719970703125000000000) * s + (&0) * t + (&0) * (s * t)`);;

let MOSER_REGION_B = prove
 (`three_label_region (moser_xi (sqrt(&3) / &2) (--(&1 / &2)))
                      (moser_ups (sqrt(&3) / &2) (--(&1 / &2)))`,
  QST_REGION_TAC
   `(&125851 / &62500) + --(&28 / &25) * s + (&0) * t + (&0) * (s * t)`
   `(&124149 / &62500) + (&28 / &25) * s + (&0) * t + (&0) * (s * t)`
   `--(&8676402310696175957215096229736642574809 / &611716844797134399414062500000000000000) + (&250472057192046156527095261029345339 / &30585842239856719970703125000000000) * s + (&0) * t + (&0) * (s * t)`);;

let MOSER_REGION_T = prove
 (`three_label_region (moser_xi (sqrt(&3)) (&0))
                      (moser_ups (sqrt(&3)) (&0))`,
  QST_REGION_TAC
   `(&288101 / &62500) + --(&56 / &25) * s + (&0) * t + (&0) * (s * t)`
   `--(&38101 / &62500) + (&56 / &25) * s + (&0) * t + (&0) * (s * t)`
   `--(&319072991677529990245663518849868194839157 / &16532887697219848632812500000000000000) + (&170400723334663086879810188701117046589 / &15292921119928359985351562500000000) * s + (&0) * t + (&0) * (s * t)`);;

let MOSER_REGION_UA = prove
 (`three_label_region (moser_xi ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12))
                      (moser_ups ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12))`,
  QST_REGION_TAC
   `(&145607 / &46875) + --(&14 / &15) * s + (&14 / &75) * t + (&149 / &1500) * (s * t)`
   `(&41893 / &46875) + (&14 / &15) * s + --(&14 / &75) * t + --(&149 / &1500) * (s * t)`
   `--(&69282889558469845970420324645415951968786761 / &445941579857110977172851562500000000000000) + (&30587621412866319752178867550184264551 / &330327096190452575683593750000000000) * s + (&108818857168190943561585642668949185123 / &44594157985711097717285156250000000000) * t + --(&6650150877379331440734593205824249381 / &12387266107141971588134765625000000000) * (s * t)`);;

let MOSER_REGION_UB = prove
 (`three_label_region (moser_xi ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12))
                      (moser_ups ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12))`,
  QST_REGION_TAC
   `(&198089 / &93750) + --(&14 / &15) * s + --(&14 / &75) * t + (&149 / &1500) * (s * t)`
   `(&176911 / &93750) + (&14 / &15) * s + (&14 / &75) * t + --(&149 / &1500) * (s * t)`
   `--(&47200452643033745845366999745678118183814261 / &445941579857110977172851562500000000000000) + (&6727236643751185204934818516078358017 / &110109032063484191894531250000000000) * s + (&1408517737016308436840218084676151327377 / &44594157985711097717285156250000000000) * t + --(&1806316599581828123874637804508071673173 / &99098128857135772705078125000000000000) * (s * t)`);;

let MOSER_REGION_UT = prove
 (`three_label_region (moser_xi (&5 * sqrt(&3) / &6) (sqrt(&33) / &6))
                      (moser_ups (&5 * sqrt(&3) / &6) (sqrt(&33) / &6))`,
  QST_REGION_TAC
   `(&288101 / &62500) + --(&28 / &15) * s + (&0) * t + (&149 / &750) * (s * t)`
   `--(&38101 / &62500) + (&28 / &15) * s + (&0) * t + --(&149 / &750) * (s * t)`
   `--(&267385685578315097288725860817742810573380343 / &16516354809522628784179687500000000000000) + (&514580822117710877865019863283994264767 / &55054516031742095947265625000000000) * s + (&507488810524818583580768302017456449 / &132130838476181030273437500000000) * t + --(&24416746749052797851970639757077439171469 / &11010903206348419189453125000000000000) * (s * t)`);;

(* ------------------------------------------------------------------------- *)
(* The eleven placed edges have length exactly one.                          *)
(* ------------------------------------------------------------------------- *)

let QST_EQ_TAC =
  REWRITE_TAC[moser_xi; moser_ups; SQRT_33_EQ] THEN
  MP_TAC(CONJ SQRT_3_POW_2 SQRT_11_POW_2) THEN
  SPEC_TAC(`sqrt(&11)`,`t:real`) THEN SPEC_TAC(`sqrt(&3)`,`s:real`) THEN
  CONV_TAC REAL_RING;;

let MOSER_EDGE_O_A = prove
 (`(moser_xi (&0) (&0) - moser_xi (sqrt(&3) / &2) (&1 / &2)) pow 2 +
   (moser_ups (&0) (&0) - moser_ups (sqrt(&3) / &2) (&1 / &2)) pow 2 = &1`,
  QST_EQ_TAC);;

let MOSER_EDGE_O_B = prove
 (`(moser_xi (&0) (&0) - moser_xi (sqrt(&3) / &2) (--(&1 / &2))) pow 2 +
   (moser_ups (&0) (&0) - moser_ups (sqrt(&3) / &2) (--(&1 / &2))) pow 2 = &1`,
  QST_EQ_TAC);;

let MOSER_EDGE_A_B = prove
 (`(moser_xi (sqrt(&3) / &2) (&1 / &2) - moser_xi (sqrt(&3) / &2) (--(&1 / &2))) pow 2 +
   (moser_ups (sqrt(&3) / &2) (&1 / &2) - moser_ups (sqrt(&3) / &2) (--(&1 / &2))) pow 2 = &1`,
  QST_EQ_TAC);;

let MOSER_EDGE_T_A = prove
 (`(moser_xi (sqrt(&3)) (&0) - moser_xi (sqrt(&3) / &2) (&1 / &2)) pow 2 +
   (moser_ups (sqrt(&3)) (&0) - moser_ups (sqrt(&3) / &2) (&1 / &2)) pow 2 = &1`,
  QST_EQ_TAC);;

let MOSER_EDGE_T_B = prove
 (`(moser_xi (sqrt(&3)) (&0) - moser_xi (sqrt(&3) / &2) (--(&1 / &2))) pow 2 +
   (moser_ups (sqrt(&3)) (&0) - moser_ups (sqrt(&3) / &2) (--(&1 / &2))) pow 2 = &1`,
  QST_EQ_TAC);;

let MOSER_EDGE_O_UA = prove
 (`(moser_xi (&0) (&0) - moser_xi ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12)) pow 2 +
   (moser_ups (&0) (&0) - moser_ups ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12)) pow 2 = &1`,
  QST_EQ_TAC);;

let MOSER_EDGE_O_UB = prove
 (`(moser_xi (&0) (&0) - moser_xi ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12)) pow 2 +
   (moser_ups (&0) (&0) - moser_ups ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12)) pow 2 = &1`,
  QST_EQ_TAC);;

let MOSER_EDGE_UA_UB = prove
 (`(moser_xi ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12) - moser_xi ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12)) pow 2 +
   (moser_ups ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12) - moser_ups ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12)) pow 2 = &1`,
  QST_EQ_TAC);;

let MOSER_EDGE_UT_UA = prove
 (`(moser_xi (&5 * sqrt(&3) / &6) (sqrt(&33) / &6) - moser_xi ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12)) pow 2 +
   (moser_ups (&5 * sqrt(&3) / &6) (sqrt(&33) / &6) - moser_ups ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12)) pow 2 = &1`,
  QST_EQ_TAC);;

let MOSER_EDGE_UT_UB = prove
 (`(moser_xi (&5 * sqrt(&3) / &6) (sqrt(&33) / &6) - moser_xi ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12)) pow 2 +
   (moser_ups (&5 * sqrt(&3) / &6) (sqrt(&33) / &6) - moser_ups ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12)) pow 2 = &1`,
  QST_EQ_TAC);;

let MOSER_EDGE_T_UT = prove
 (`(moser_xi (sqrt(&3)) (&0) - moser_xi (&5 * sqrt(&3) / &6) (sqrt(&33) / &6)) pow 2 +
   (moser_ups (sqrt(&3)) (&0) - moser_ups (&5 * sqrt(&3) / &6) (sqrt(&33) / &6)) pow 2 = &1`,
  QST_EQ_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Moser graph has no proper three-colouring (vertex order O,A,B,T,uA,uB,uT).*)
(* ------------------------------------------------------------------------- *)

let MOSER_FORCED = prove
 (`!a b c d. a < 3 /\ b < 3 /\ c < 3 /\ d < 3 /\
             ~(a = b) /\ ~(a = c) /\ ~(b = c) /\ ~(d = b) /\ ~(d = c)
             ==> d = a`,
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Combined: no 3-labelling of the seven placed points avoids a monochromatic *)
(* unit pair, and all seven lie in the three-label region.                    *)
(* ------------------------------------------------------------------------- *)

let MOSER_PLACEMENT_CERTIFICATE = prove
 (`three_label_region (moser_xi (&0) (&0)) (moser_ups (&0) (&0)) /\
      three_label_region (moser_xi (sqrt(&3) / &2) (&1 / &2)) (moser_ups (sqrt(&3) / &2) (&1 / &2)) /\
      three_label_region (moser_xi (sqrt(&3) / &2) (--(&1 / &2))) (moser_ups (sqrt(&3) / &2) (--(&1 / &2))) /\
      three_label_region (moser_xi (sqrt(&3)) (&0)) (moser_ups (sqrt(&3)) (&0)) /\
      three_label_region (moser_xi ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12)) (moser_ups ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12)) /\
      three_label_region (moser_xi ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12)) (moser_ups ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12)) /\
      three_label_region (moser_xi (&5 * sqrt(&3) / &6) (sqrt(&33) / &6)) (moser_ups (&5 * sqrt(&3) / &6) (sqrt(&33) / &6)) /\
   ~(?c:real#real->num.
       (!p. c p < 3) /\
       (!x1 y1 x2 y2.
          MEM (x1,y1) [(moser_xi (&0) (&0), moser_ups (&0) (&0));
      (moser_xi (sqrt(&3) / &2) (&1 / &2), moser_ups (sqrt(&3) / &2) (&1 / &2));
      (moser_xi (sqrt(&3) / &2) (--(&1 / &2)), moser_ups (sqrt(&3) / &2) (--(&1 / &2)));
      (moser_xi (sqrt(&3)) (&0), moser_ups (sqrt(&3)) (&0));
      (moser_xi ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12), moser_ups ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12));
      (moser_xi ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12), moser_ups ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12));
      (moser_xi (&5 * sqrt(&3) / &6) (sqrt(&33) / &6), moser_ups (&5 * sqrt(&3) / &6) (sqrt(&33) / &6))] /\
          MEM (x2,y2) [(moser_xi (&0) (&0), moser_ups (&0) (&0));
      (moser_xi (sqrt(&3) / &2) (&1 / &2), moser_ups (sqrt(&3) / &2) (&1 / &2));
      (moser_xi (sqrt(&3) / &2) (--(&1 / &2)), moser_ups (sqrt(&3) / &2) (--(&1 / &2)));
      (moser_xi (sqrt(&3)) (&0), moser_ups (sqrt(&3)) (&0));
      (moser_xi ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12), moser_ups ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12));
      (moser_xi ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12), moser_ups ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12));
      (moser_xi (&5 * sqrt(&3) / &6) (sqrt(&33) / &6), moser_ups (&5 * sqrt(&3) / &6) (sqrt(&33) / &6))] /\
          (x1 - x2) pow 2 + (y1 - y2) pow 2 = &1
          ==> ~(c(x1,y1) = c(x2,y2))))`,
  REWRITE_TAC[MOSER_REGION_O; MOSER_REGION_A; MOSER_REGION_B; MOSER_REGION_T; MOSER_REGION_UA; MOSER_REGION_UB; MOSER_REGION_UT] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `c:real#real->num` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun prop ->
    let use th =
      let l,_ = dest_eq(concl th) in
      let d1,d2 = dest_binop `(+):real->real->real` l in
      let dx = lhand d1 and dy = lhand d2 in
      let x1,x2 = dest_binop `(-):real->real->real` dx
      and y1,y2 = dest_binop `(-):real->real->real` dy in
      let ith = SPECL [x1;y1;x2;y2] prop in
      MP ith (CONJ (EQT_ELIM(REWRITE_CONV[MEM] (lhand(lhand(concl ith)))))
                   (CONJ (EQT_ELIM(REWRITE_CONV[MEM]
                                     (lhand(rand(lhand(concl ith))))))
                         th)) in
    MAP_EVERY (ASSUME_TAC o use)
     [MOSER_EDGE_O_A; MOSER_EDGE_O_B; MOSER_EDGE_A_B; MOSER_EDGE_T_A; MOSER_EDGE_T_B; MOSER_EDGE_O_UA; MOSER_EDGE_O_UB; MOSER_EDGE_UA_UB; MOSER_EDGE_UT_UA; MOSER_EDGE_UT_UB; MOSER_EDGE_T_UT]) THEN

  SUBGOAL_THEN `(c:real#real->num)(moser_xi (sqrt(&3)) (&0),moser_ups (sqrt(&3)) (&0)) = (c:real#real->num)(moser_xi (&0) (&0),moser_ups (&0) (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOSER_FORCED THEN
    EXISTS_TAC `(c:real#real->num)(moser_xi (sqrt(&3) / &2) (&1 / &2),moser_ups (sqrt(&3) / &2) (&1 / &2))` THEN EXISTS_TAC `(c:real#real->num)(moser_xi (sqrt(&3) / &2) (--(&1 / &2)),moser_ups (sqrt(&3) / &2) (--(&1 / &2)))` THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real#real->num)(moser_xi (&5 * sqrt(&3) / &6) (sqrt(&33) / &6),moser_ups (&5 * sqrt(&3) / &6) (sqrt(&33) / &6)) = (c:real#real->num)(moser_xi (&0) (&0),moser_ups (&0) (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOSER_FORCED THEN
    EXISTS_TAC `(c:real#real->num)(moser_xi ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12),moser_ups ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12))` THEN EXISTS_TAC `(c:real#real->num)(moser_xi ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12),moser_ups ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12))` THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;
