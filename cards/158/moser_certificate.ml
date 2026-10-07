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
    (&35 * (gx - &290 / &250) - &12 * (gy + &149 / &250)) / &37`;;

let moser_ups = new_definition
 `moser_ups (gx:real) (gy:real) =
    (&12 * (gx - &290 / &250) + &35 * (gy + &149 / &250)) / &37`;;

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
   `(&106301 / &62500) + (&0) * s + (&0) * t + (&0) * (s * t)`
   `(&143699 / &62500) + (&0) * s + (&0) * t + (&0) * (s * t)`
   `(&319835183522319532260768268201282088391 / &611716844797134399414062500000000000000) + (&0) * s + (&0) * t + (&0) * (s * t)`);;

let MOSER_REGION_A = prove
 (`three_label_region (moser_xi (sqrt(&3) / &2) (&1 / &2))
                      (moser_ups (sqrt(&3) / &2) (&1 / &2))`,
  QST_REGION_TAC
   `(&206051 / &62500) + --(&29 / &25) * s + (&0) * t + (&0) * (s * t)`
   `(&43949 / &62500) + (&29 / &25) * s + (&0) * t + (&0) * (s * t)`
   `--(&286965675353444539232794327295438388135609 / &611716844797134399414062500000000000000) + (&33138076741224775839839230519560970833 / &122343368959426879882812500000000000) * s + (&0) * t + (&0) * (s * t)`);;

let MOSER_REGION_B = prove
 (`three_label_region (moser_xi (sqrt(&3) / &2) (--(&1 / &2)))
                      (moser_ups (sqrt(&3) / &2) (--(&1 / &2)))`,
  QST_REGION_TAC
   `(&131551 / &62500) + --(&29 / &25) * s + (&0) * t + (&0) * (s * t)`
   `(&118449 / &62500) + (&29 / &25) * s + (&0) * t + (&0) * (s * t)`
   `--(&483273794172982826657222981727153616557 / &16532887697219848632812500000000000000) + (&2064784294604875482735207892327803333 / &122343368959426879882812500000000000) * s + (&0) * t + (&0) * (s * t)`);;

let MOSER_REGION_T = prove
 (`three_label_region (moser_xi (sqrt(&3)) (&0))
                      (moser_ups (sqrt(&3)) (&0))`,
  QST_REGION_TAC
   `(&293801 / &62500) + --(&58 / &25) * s + (&0) * t + (&0) * (s * t)`
   `--(&43801 / &62500) + (&58 / &25) * s + (&0) * t + (&0) * (s * t)`
   `--(&14280657570967382447807885017288294521786609 / &611716844797134399414062500000000000000) + (&824494306670438776168514130773100637083 / &61171684479713439941406250000000000) * s + (&0) * t + (&0) * (s * t)`);;

let MOSER_REGION_UA = prove
 (`three_label_region (moser_xi ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12))
                      (moser_ups ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12))`,
  QST_REGION_TAC
   `(&149882 / &46875) + --(&29 / &30) * s + (&29 / &150) * t + (&149 / &1500) * (s * t)`
   `(&37618 / &46875) + (&29 / &30) * s + --(&29 / &150) * t + --(&149 / &1500) * (s * t)`
   `--(&95967522919388556184685035429907820515892961 / &445941579857110977172851562500000000000000) + (&55963952572184108871610474640896378499 / &440436128253936767578125000000000000) * s + --(&271485981183553110703967958311949642419 / &178376631942844390869140625000000000000) * t + (&42773785562566367228987078045290449863 / &24774532214283943176269531250000000000) * (s * t)`);;

let MOSER_REGION_UB = prove
 (`three_label_region (moser_xi ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12))
                      (moser_ups ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12))`,
  QST_REGION_TAC
   `(&206639 / &93750) + --(&29 / &30) * s + --(&29 / &150) * t + (&149 / &1500) * (s * t)`
   `(&168361 / &93750) + (&29 / &30) * s + (&29 / &150) * t + --(&149 / &1500) * (s * t)`
   `--(&67378720917530597721211907352548510764670461 / &445941579857110977172851562500000000000000) + (&115227136258642123606222682409309831997 / &1321308384761810302734375000000000000) * s + (&8089385161664327891016661394916382479919 / &178376631942844390869140625000000000000) * t + --(&2593471752210572531589798382070393066173 / &99098128857135772705078125000000000000) * (s * t)`);;

let MOSER_REGION_UT = prove
 (`three_label_region (moser_xi (&5 * sqrt(&3) / &6) (sqrt(&33) / &6))
                      (moser_ups (&5 * sqrt(&3) / &6) (sqrt(&33) / &6))`,
  QST_REGION_TAC
   `(&293801 / &62500) + --(&29 / &15) * s + (&0) * t + (&149 / &750) * (s * t)`
   `--(&43801 / &62500) + (&29 / &15) * s + (&0) * t + --(&149 / &750) * (s * t)`
   `--(&316028408556202856003605560559735601111050943 / &16516354809522628784179687500000000000000) + (&2432816086439925742596562933352341286249 / &220218064126968383789062500000000000) * s + (&2356981803295001360193855069310539403 / &528523353904724121093750000000000) * t + --(&28349651943682871191636267637506724237969 / &11010903206348419189453125000000000000) * (s * t)`);;

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
