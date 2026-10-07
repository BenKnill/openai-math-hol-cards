(* ========================================================================= *)
(* NEGATIVE CONTROL: SC_F has (x2 - x4) in place of (x2 + x4); must FAIL.   *)
(* Family 049, paper                                                         *)
(*   A-stable-coordinate-that-is-not-a-coordinate-in-four-variables-         *)
(*   October-5-2026, Section 2 (Props 2.1 and 2.2), assembled.               *)
(*                                                                           *)
(* Final theorem SC049_STABLE_COORDINATE: explicit maps                      *)
(*   SC_PHI : (p,s,u,N,w') |-> (x1,x2,x3,x4,w)                               *)
(*   SC_PSI : (x1,x2,x3,x4,w) |-> (p,s,u,N,w')                               *)
(* are mutually inverse on R^5, and f(SC_PHI z) = first coordinate of z,     *)
(* where f(x1,x2,x3,x4) = x1 - 2Q(Q(x2+x4) + x1 x4), Q = x2^2 - x4^2 + x1 x3. *)
(*                                                                           *)
(* SC_PHI = iota o flow_w o pi  and  SC_PSI = pi^-1 o flow_{-w} o iota^-1,   *)
(* the point maps of the paper's three ring isomorphisms                     *)
(*   R[w] -> A[w] (Prop 2.1),  A[w] -> P[w]/(H+pw) (exp(w Delta)),           *)
(*   P[w]/(H+pw) -> k[p,s,u,N,w'] (linear coordinates L,N and w' = w + Q0).  *)
(* Both maps are visibly polynomial with rational coefficients (the only     *)
(* division is by 2). Polynomial maps that agree on R^5 agree as polynomials,*)
(* so this gives a Q-algebra automorphism of Q[x1..x4,w], hence of           *)
(* C[x1..x4,w], sending f to x1. That deduction is NOT formalised here.      *)
(* Also NOT covered: the hard half of Theorem 1.1, that f is not a           *)
(* coordinate of C[x1..x4].                                                  *)
(*                                                                           *)
(* Variable names: the paper's F, J are a, j (F and T are HOL constants).    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

let XX = new_definition
 `XX(p:real,s:real,u:real,a:real,j:real) = s pow 2 - u pow 2 + p * a`;;

let HH = new_definition
 `HH(p:real,s:real,u:real,a:real,j:real) =
    XX(p,s,u,a,j) pow 2 * a - (&1 + &2 * s * XX(p,s,u,a,j)) * j -
    p * j pow 2 - u`;;

let LL = new_definition
 `LL(p:real,s:real,u:real,a:real,j:real) =
    (s pow 2 - u pow 2) pow 2 * a - (&1 + &2 * s * (s pow 2 - u pow 2)) * j`;;

let QZ = new_definition
 `QZ(p:real,s:real,u:real,a:real,j:real) =
    &2 * (s pow 2 - u pow 2) * a pow 2 + p * a pow 3 - &2 * s * a * j -
    j pow 2`;;

(* exp(w Delta) on the generators p,s,u,F,J (it fixes x = XX).              *)
let FLOW = new_definition
 `FLOW(w:real,p:real,s:real,u:real,a:real,j:real) =
    (p,
     s + XX(p,s,u,a,j) * w * p * (&2 * u - w * p),
     u - w * p,
     a - XX(p,s,u,a,j) * w * (&2 * u - w * p) *
         (&2 * s + XX(p,s,u,a,j) * w * p * (&2 * u - w * p)) -
     &2 * u * w + w pow 2 * p,
     j - XX(p,s,u,a,j) pow 2 * w * (&2 * u - w * p))`;;

(* pi: k[p,s,u,N,w'] -> P[w]/(H + p w): L = u - p w', F,J from (L,N),       *)
(* w = w' - Q0. Output is (w, p, s, u, F, J).                                *)
let PSTAR = new_definition
 `PSTAR(p:real,s:real,u:real,n:real,v:real) =
    (v - QZ(p,s,u,
            &4 * s pow 2 * (u - p * v) +
            (&1 + &2 * s * (s pow 2 - u pow 2)) * n,
            --(&1 - &2 * s * (s pow 2 - u pow 2)) * (u - p * v) +
            (s pow 2 - u pow 2) pow 2 * n),
     p, s, u,
     &4 * s pow 2 * (u - p * v) + (&1 + &2 * s * (s pow 2 - u pow 2)) * n,
     --(&1 - &2 * s * (s pow 2 - u pow 2)) * (u - p * v) +
     (s pow 2 - u pow 2) pow 2 * n)`;;

let PINV = new_definition
 `PINV(w:real,p:real,s:real,u:real,a:real,j:real) =
    (p, s, u,
     (&1 - &2 * s * (s pow 2 - u pow 2)) * a + &4 * s pow 2 * j,
     w + QZ(p,s,u,a,j))`;;

let YY = new_definition
 `YY(x1:real,x2:real,x3:real,x4:real,w:real) = x2 pow 2 - x4 pow 2 + x1 * x3`;;

(* iota: (w, point of V(H)) |-> (p', s', F', J, w), Prop 2.1.               *)
let IOTA = new_definition
 `IOTA(w:real,p:real,s:real,u:real,a:real,j:real) =
    (&2 * XX(p,s,u,a,j) pow 2 * (s - u) + (&1 + &2 * XX(p,s,u,a,j) * j) * p,
     ((&1 - &2 * j * XX(p,s,u,a,j)) * (s - u) - &2 * j pow 2 * p) +
     (u - a * XX(p,s,u,a,j) pow 2 + &2 * s * XX(p,s,u,a,j) * j +
      p * j pow 2),
     (&1 - &2 * j * XX(p,s,u,a,j)) * a + &2 * j pow 2 * (s + u),
     j, w)`;;

(* iota^-1: M = (I + 2 n e^t) M' with s' - u' = x2 + x4, s' + u' = x2 - x4. *)
let IINV = new_definition
 `IINV(x1:real,x2:real,x3:real,x4:real,w:real) =
    (w,
     (&1 - &2 * YY(x1,x2,x3,x4,w) * x4) * x1 -
     &2 * YY(x1,x2,x3,x4,w) pow 2 * (x2 + x4),
     (((&1 + &2 * x4 * YY(x1,x2,x3,x4,w)) * (x2 + x4) + &2 * x4 pow 2 * x1) +
      (&2 * YY(x1,x2,x3,x4,w) pow 2 * x3 +
       (&1 - &2 * YY(x1,x2,x3,x4,w) * x4) * (x2 - x4))) / &2,
     ((&2 * YY(x1,x2,x3,x4,w) pow 2 * x3 +
       (&1 - &2 * YY(x1,x2,x3,x4,w) * x4) * (x2 - x4)) -
      ((&1 + &2 * x4 * YY(x1,x2,x3,x4,w)) * (x2 + x4) +
       &2 * x4 pow 2 * x1)) / &2,
     (&1 + &2 * x4 * YY(x1,x2,x3,x4,w)) * x3 - &2 * x4 pow 2 * (x2 - x4),
     x4)`;;

(* The paper's f, read on the first four coordinates.                       *)
let SC_F = new_definition
 `SC_F(x1:real,x2:real,x3:real,x4:real,w:real) =
    x1 - &2 * YY(x1,x2,x3,x4,w) *
         (YY(x1,x2,x3,x4,w) * (x2 - x4) + x1 * x4)`;;

let SC_PHI = new_definition
 `SC_PHI (z:real#real#real#real#real) =
    IOTA(FST(PSTAR z), FLOW(PSTAR z))`;;

let SC_PSI = new_definition
 `SC_PSI (y:real#real#real#real#real) =
    PINV(FST(IINV y), FLOW(--(FST(IINV y)), SND(IINV y)))`;;

(* ------------------------------------------------------------------------- *)
(* The flow.                                                                 *)
(* ------------------------------------------------------------------------- *)

let SCA_FLOW_XX = prove
 (`!w p s u a j. XX(FLOW(w,p,s,u,a,j)) = XX(p,s,u,a,j)`,
  REWRITE_TAC[FLOW] THEN REWRITE_TAC[XX] THEN CONV_TAC REAL_RING);;

let SCA_FLOW_HH = prove
 (`!w p s u a j. HH(FLOW(w,p,s,u,a,j)) = HH(p,s,u,a,j) + p * w`,
  REWRITE_TAC[FLOW] THEN REWRITE_TAC[HH] THEN
  REWRITE_TAC[REWRITE_RULE[FLOW] SCA_FLOW_XX] THEN
  REWRITE_TAC[XX] THEN CONV_TAC REAL_RING);;

let SCA_FLOW_INV = prove
 (`!w p s u a j. FLOW(--w, FLOW(w,p,s,u,a,j)) = (p,s,u,a,j)`,
  REWRITE_TAC[FLOW] THEN REWRITE_TAC[REWRITE_RULE[FLOW] SCA_FLOW_XX] THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT CONJ_TAC THEN CONV_TAC REAL_RING);;

let SCA_P_FLOW_HH = prove
 (`!w q. HH(FLOW(w,q)) = HH q + FST q * w`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SCA_FLOW_HH]);;

let SCA_P_FLOW_FST = prove
 (`!w q. FST(FLOW(w,q)) = FST q`,
  REWRITE_TAC[FORALL_PAIR_THM; FLOW; FST]);;

let SCA_P_FLOW_INV = prove
 (`!w q. FLOW(--w, FLOW(w,q)) = q`,
  REWRITE_TAC[FORALL_PAIR_THM; SCA_FLOW_INV]);;

let SCA_P_FLOW_INV2 = prove
 (`!w q. FLOW(w, FLOW(--w,q)) = q`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`--w:real`; `q:real#real#real#real#real`] SCA_P_FLOW_INV) THEN
  REWRITE_TAC[REAL_NEG_NEG]);;

let SCA_P_FLOW_HH1 = prove
 (`!y. HH(FLOW y) = HH(SND y) + FST(SND y) * FST y`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND; SCA_FLOW_HH]);;

let SCA_P_FLOW_INV1 = prove
 (`!y. FLOW(--(FST y), FLOW y) = SND y`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND; SCA_FLOW_INV]);;

let SCA_P_FLOW_FST1 = prove
 (`!y. FST(FLOW y) = FST(SND y)`,
  REWRITE_TAC[FORALL_PAIR_THM; FLOW; FST; SND]);;

(* ------------------------------------------------------------------------- *)
(* The linear coordinates (L,N) and pi.                                      *)
(* ------------------------------------------------------------------------- *)

let SCA_H_SPLIT = prove
 (`!p s u a j. HH(p,s,u,a,j) = LL(p,s,u,a,j) - u + p * QZ(p,s,u,a,j)`,
  REWRITE_TAC[HH; XX; LL; QZ] THEN CONV_TAC REAL_RING);;

let SCA_LL_PSTAR = prove
 (`!p s u n v.
     LL(p,s,u,
        &4 * s pow 2 * (u - p * v) + (&1 + &2 * s * (s pow 2 - u pow 2)) * n,
        --(&1 - &2 * s * (s pow 2 - u pow 2)) * (u - p * v) +
        (s pow 2 - u pow 2) pow 2 * n) = u - p * v`,
  REWRITE_TAC[LL] THEN CONV_TAC REAL_RING);;

let SCA_LIN_A = prove
 (`!p s u a j.
     &4 * s pow 2 * LL(p,s,u,a,j) +
     (&1 + &2 * s * (s pow 2 - u pow 2)) *
     ((&1 - &2 * s * (s pow 2 - u pow 2)) * a + &4 * s pow 2 * j) = a`,
  REWRITE_TAC[LL] THEN CONV_TAC REAL_RING);;

let SCA_LIN_J = prove
 (`!p s u a j.
     --(&1 - &2 * s * (s pow 2 - u pow 2)) * LL(p,s,u,a,j) +
     (s pow 2 - u pow 2) pow 2 *
     ((&1 - &2 * s * (s pow 2 - u pow 2)) * a + &4 * s pow 2 * j) = j`,
  REWRITE_TAC[LL] THEN CONV_TAC REAL_RING);;

let SCA_P_PSTAR_ON = prove
 (`!z. HH(SND(PSTAR z)) + FST(SND(PSTAR z)) * FST(PSTAR z) = &0`,
  REWRITE_TAC[FORALL_PAIR_THM; PSTAR; FST; SND] THEN
  REWRITE_TAC[SCA_H_SPLIT; SCA_LL_PSTAR] THEN CONV_TAC REAL_RING);;

let SCA_P_PINV_PSTAR = prove
 (`!z. PINV(PSTAR z) = z`,
  REWRITE_TAC[FORALL_PAIR_THM; PSTAR; PINV; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN CONV_TAC REAL_RING);;

let SCA_PSTAR_PINV = prove
 (`!w p s u a j.
     HH(p,s,u,a,j) + p * w = &0 ==> PSTAR(PINV(w,p,s,u,a,j)) = (w,p,s,u,a,j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SCA_H_SPLIT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `u - p * (w + QZ(p,s,u,a,j)) = LL(p,s,u,a,j)` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[PINV] THEN REWRITE_TAC[PSTAR] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[SCA_LIN_A; SCA_LIN_J; PAIR_EQ] THEN REAL_ARITH_TAC);;

let SCA_P_PSTAR_PINV = prove
 (`!w q. HH q + FST q * w = &0 ==> PSTAR(PINV(w,q)) = (w,q)`,
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN MESON_TAC[SCA_PSTAR_PINV]);;

(* ------------------------------------------------------------------------- *)
(* iota and its inverse (Prop 2.1).                                          *)
(* ------------------------------------------------------------------------- *)

let SCA_IINV_XX = prove
 (`!x1 x2 x3 x4 w. XX(SND(IINV(x1,x2,x3,x4,w))) = YY(x1,x2,x3,x4,w)`,
  REWRITE_TAC[IINV; SND] THEN REWRITE_TAC[XX; YY] THEN CONV_TAC REAL_FIELD);;

let SCA_P_IINV_ON = prove
 (`!y. HH(SND(IINV y)) = &0`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[IINV; SND] THEN REWRITE_TAC[HH] THEN
  REWRITE_TAC[REWRITE_RULE[IINV; SND] SCA_IINV_XX] THEN
  CONV_TAC REAL_FIELD);;

let SCA_P_IOTA_IINV = prove
 (`!y. IOTA(IINV y) = y`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[IINV] THEN REWRITE_TAC[IOTA] THEN
  REWRITE_TAC[REWRITE_RULE[IINV; SND] SCA_IINV_XX] THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT CONJ_TAC THEN CONV_TAC REAL_FIELD);;

let SCA_X_IOTA = prove
 (`!w p s u a j.
     HH(p,s,u,a,j) = &0 ==> YY(IOTA(w,p,s,u,a,j)) = XX(p,s,u,a,j)`,
  REWRITE_TAC[IOTA; YY; HH; XX] THEN CONV_TAC REAL_RING);;

let SCA_IINV_IOTA = prove
 (`!w p s u a j.
     HH(p,s,u,a,j) = &0 ==> IINV(IOTA(w,p,s,u,a,j)) = (w,p,s,u,a,j)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[IOTA] o SPEC `w:real` o
              MATCH_MP (MESON[SCA_X_IOTA]
                `HH(p,s,u,a,j) = &0
                 ==> !w. YY(IOTA(w,p,s,u,a,j)) = XX(p,s,u,a,j)`)) THEN
  REWRITE_TAC[IOTA] THEN REWRITE_TAC[IINV] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `HH(p,s,u,a,j) = &0` THEN REWRITE_TAC[HH] THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
  UNDISCH_TAC
   `XX(p,s,u,a,j) pow 2 * a - (&1 + &2 * s * XX(p,s,u,a,j)) * j -
    p * j pow 2 - u = &0` THEN
  CONV_TAC REAL_FIELD);;

let SCA_F_IOTA = prove
 (`!w p s u a j. HH(p,s,u,a,j) = &0 ==> SC_F(IOTA(w,p,s,u,a,j)) = p`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[IOTA] o SPEC `w:real` o
              MATCH_MP (MESON[SCA_X_IOTA]
                `HH(p,s,u,a,j) = &0
                 ==> !w. YY(IOTA(w,p,s,u,a,j)) = XX(p,s,u,a,j)`)) THEN
  REWRITE_TAC[IOTA] THEN REWRITE_TAC[SC_F] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `HH(p,s,u,a,j) = &0` THEN REWRITE_TAC[HH] THEN
  CONV_TAC REAL_RING);;

let SCA_P_IINV_IOTA = prove
 (`!w q. HH q = &0 ==> IINV(IOTA(w,q)) = (w,q)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[SCA_IINV_IOTA]);;

let SCA_P_F_IOTA = prove
 (`!w q. HH q = &0 ==> SC_F(IOTA(w,q)) = FST q`,
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN MESON_TAC[SCA_F_IOTA]);;

(* ------------------------------------------------------------------------- *)
(* Assembly.                                                                 *)
(* ------------------------------------------------------------------------- *)

let SC049_PSI_PHI = prove
 (`!z. SC_PSI(SC_PHI z) = z`,
  GEN_TAC THEN REWRITE_TAC[SC_PHI; SC_PSI] THEN
  SUBGOAL_THEN `HH(FLOW(PSTAR z)) = &0` ASSUME_TAC THENL
   [REWRITE_TAC[SCA_P_FLOW_HH1; SCA_P_PSTAR_ON]; ALL_TAC] THEN
  ASM_SIMP_TAC[SCA_P_IINV_IOTA; FST; SND; SCA_P_FLOW_INV1] THEN
  REWRITE_TAC[PAIR; SCA_P_PINV_PSTAR]);;

let SC049_PHI_PSI = prove
 (`!y. SC_PHI(SC_PSI y) = y`,
  GEN_TAC THEN REWRITE_TAC[SC_PHI; SC_PSI] THEN
  SUBGOAL_THEN
   `HH(FLOW(--(FST(IINV y)), SND(IINV y))) +
    FST(FLOW(--(FST(IINV y)), SND(IINV y))) * FST(IINV y) = &0`
  ASSUME_TAC THENL
   [REWRITE_TAC[SCA_P_FLOW_HH; SCA_P_FLOW_FST; SCA_P_IINV_ON] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_SIMP_TAC[SCA_P_PSTAR_PINV; FST; SND; SCA_P_FLOW_INV2] THEN
  REWRITE_TAC[PAIR; SCA_P_IOTA_IINV]);;

let SC049_F_PHI = prove
 (`!p s u n v. SC_F(SC_PHI(p,s,u,n,v)) = p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SC_PHI] THEN
  SUBGOAL_THEN `HH(FLOW(PSTAR(p,s,u,n,v))) = &0` ASSUME_TAC THENL
   [REWRITE_TAC[SCA_P_FLOW_HH1; SCA_P_PSTAR_ON]; ALL_TAC] THEN
  ASM_SIMP_TAC[SCA_P_F_IOTA; SCA_P_FLOW_FST1] THEN
  REWRITE_TAC[PSTAR; FST; SND]);;

(* The stable-coordinate assertion, as a statement about explicit maps.      *)
let SC049_STABLE_COORDINATE = prove
 (`(!z. SC_PSI(SC_PHI z) = z) /\
   (!y. SC_PHI(SC_PSI y) = y) /\
   (!p s u n v. SC_F(SC_PHI(p,s,u,n,v)) = p)`,
  REWRITE_TAC[SC049_PSI_PHI; SC049_PHI_PSI; SC049_F_PHI]);;
