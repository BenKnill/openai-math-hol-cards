(* ========================================================================= *)
(* Family 049, paper                                                         *)
(*   A-stable-coordinate-that-is-not-a-coordinate-in-four-variables-         *)
(*   October-5-2026, Section 2 (sections/02-construction.tex).               *)
(*                                                                           *)
(* HOL Light check of the explicit polynomial identities behind the          *)
(* "stable coordinate" half of Theorem 1.1: after adjoining one variable w,  *)
(* the degree-5 polynomial f becomes a coordinate.                           *)
(*                                                                           *)
(* Variables: p s u a j w stand for the paper's p s u F J w (F and T are     *)
(* reserved constants in HOL, so F is renamed a).                            *)
(*   x = s^2 - u^2 + p F,  H = x^2 F - (1 + 2 s x) J - p J^2 - u.            *)
(*                                                                           *)
(* All statements are universally quantified identities over the reals.      *)
(* Every identity has integer coefficients, so it is an identity in          *)
(* Z[p,s,u,F,J,w] and therefore holds in C[...] as the paper needs.          *)
(* NOT covered: that these substitutions assemble into the claimed           *)
(* automorphism of C[x1..x4,w] (ring-theoretic glue in the paper), and the   *)
(* hard half of the theorem (f is NOT a coordinate of C[x1..x4]).            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Prop 2.1 (polynomial change of coordinates), matrix M' = (I - 2 n e^t) M. *)
(* ap = F', d = s' - u', e = s' + u', pp = p', up = u'.                      *)
(* ------------------------------------------------------------------------- *)

let SC049_DET_PRESERVED = prove
 (`!p s u a j x ap d e pp.
     x = s pow 2 - u pow 2 + p * a /\
     ap = (&1 - &2 * j * x) * a + &2 * j pow 2 * (s + u) /\
     d = (&1 - &2 * j * x) * (s - u) - &2 * j pow 2 * p /\
     e = -- &2 * x pow 2 * a + (&1 + &2 * x * j) * (s + u) /\
     pp = &2 * x pow 2 * (s - u) + (&1 + &2 * x * j) * p
     ==> d * e + pp * ap = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING);;

let SC049_H_LINEAR = prove
 (`!p s u a j x d e up.
     x = s pow 2 - u pow 2 + p * a /\
     d = (&1 - &2 * j * x) * (s - u) - &2 * j pow 2 * p /\
     e = -- &2 * x pow 2 * a + (&1 + &2 * x * j) * (s + u) /\
     up = u - a * x pow 2 + &2 * s * x * j + p * j pow 2
     ==> &2 * up = e - d /\
         x pow 2 * a - (&1 + &2 * s * x) * j - p * j pow 2 - u = --j - up`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN CONV_TAC REAL_RING);;

let SC049_P_FORMULA = prove
 (`!p s u a j x d pp.
     x = s pow 2 - u pow 2 + p * a /\
     d = (&1 - &2 * j * x) * (s - u) - &2 * j pow 2 * p /\
     pp = &2 * x pow 2 * (s - u) + (&1 + &2 * x * j) * p
     ==> p = pp - &2 * x * (x * d + pp * j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING);;

(* Inverse substitution M = (I + 2 n e^t) M', entrywise.                     *)
let SC049_MATRIX_INVERSE = prove
 (`!p s u a j x ap d e pp.
     x = s pow 2 - u pow 2 + p * a /\
     ap = (&1 - &2 * j * x) * a + &2 * j pow 2 * (s + u) /\
     d = (&1 - &2 * j * x) * (s - u) - &2 * j pow 2 * p /\
     e = -- &2 * x pow 2 * a + (&1 + &2 * x * j) * (s + u) /\
     pp = &2 * x pow 2 * (s - u) + (&1 + &2 * x * j) * p
     ==> (&1 + &2 * j * x) * ap - &2 * j pow 2 * e = a /\
         (&1 + &2 * j * x) * d + &2 * j pow 2 * pp = s - u /\
         &2 * x pow 2 * ap + (&1 - &2 * x * j) * e = s + u /\
         &2 * x pow 2 * d - (&1 - &2 * x * j) * pp = --p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Prop 2.2 (one-variable stabilization).                                    *)
(* ------------------------------------------------------------------------- *)

(* Equation (con:quadric-identity): x y - z (z + 1) = p (H + u).             *)
let SC049_QUADRIC_IDENTITY = prove
 (`!p s u a j x y z.
     x = s pow 2 - u pow 2 + p * a /\
     y = s + x * (x + u pow 2) /\
     z = s * x + p * j
     ==> x * y - z * (z + &1) =
         p * ((x pow 2 * a - (&1 + &2 * s * x) * j - p * j pow 2 - u) + u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING);;

(* The flow exp(w Delta) of the locally nilpotent derivation                 *)
(* Delta = -p d/du (in coordinates p,x,y,z,u), written out on the            *)
(* generators p,s,u,F,J of P. It fixes p and x, and sends H to H + p w.      *)
let SC049_FLOW_FIXES_X_AND_SHIFTS_H = prove
 (`!p s u a j w x s1 u1 a1 j1.
     x = s pow 2 - u pow 2 + p * a /\
     s1 = s + x * w * p * (&2 * u - w * p) /\
     u1 = u - w * p /\
     a1 = a - x * w * (&2 * u - w * p) *
              (&2 * s + x * w * p * (&2 * u - w * p)) -
          &2 * u * w + w pow 2 * p /\
     j1 = j - x pow 2 * w * (&2 * u - w * p)
     ==> s1 pow 2 - u1 pow 2 + p * a1 = x /\
         (s1 pow 2 - u1 pow 2 + p * a1) pow 2 * a1 -
         (&1 + &2 * s1 * (s1 pow 2 - u1 pow 2 + p * a1)) * j1 -
         p * j1 pow 2 - u1 =
         (x pow 2 * a - (&1 + &2 * s * x) * j - p * j pow 2 - u) + p * w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `s1 pow 2 - u1 pow 2 + p * a1 = x` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING]);;

(* The flow at -w undoes the flow at w. Here x in the -w step stands for    *)
(* the image of x under the w step, which equals x by the theorem above.    *)
let SC049_FLOW_INVERSE = prove
 (`!p s u a j w x s1 u1 a1 j1.
     x = s pow 2 - u pow 2 + p * a /\
     s1 = s + x * w * p * (&2 * u - w * p) /\
     u1 = u - w * p /\
     a1 = a - x * w * (&2 * u - w * p) *
              (&2 * s + x * w * p * (&2 * u - w * p)) -
          &2 * u * w + w pow 2 * p /\
     j1 = j - x pow 2 * w * (&2 * u - w * p)
     ==> s1 + x * (--w) * p * (&2 * u1 - (--w) * p) = s /\
         u1 - (--w) * p = u /\
         a1 - x * (--w) * (&2 * u1 - (--w) * p) *
              (&2 * s1 + x * (--w) * p * (&2 * u1 - (--w) * p)) -
         &2 * u1 * (--w) + (--w) pow 2 * p = a /\
         j1 - x pow 2 * (--w) * (&2 * u1 - (--w) * p) = j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    let l = lhs(concl th) in
    if is_var l && mem (fst(dest_var l)) ["s1";"u1";"a1";"j1"]
    then SUBST_ALL_TAC th else failwith "skip")) THEN
  REPEAT CONJ_TAC THEN CONV_TAC REAL_RING);;

(* Equations (con:linear-coordinates)-(con:H-expansion): the unimodular      *)
(* linear change (F,J) <-> (L,N) over k[s,u], and H = L - u + p Q0.          *)
let SC049_LINEAR_COORDINATES = prove
 (`!p s u a j x0 l n q0.
     x0 = s pow 2 - u pow 2 /\
     l = x0 pow 2 * a - (&1 + &2 * s * x0) * j /\
     n = (&1 - &2 * s * x0) * a + &4 * s pow 2 * j /\
     q0 = &2 * x0 * a pow 2 + p * a pow 3 - &2 * s * a * j - j pow 2
     ==> &4 * s pow 2 * x0 pow 2 + (&1 + &2 * s * x0) * (&1 - &2 * s * x0) = &1 /\
         &4 * s pow 2 * l + (&1 + &2 * s * x0) * n = a /\
         --(&1 - &2 * s * x0) * l + x0 pow 2 * n = j /\
         (x0 + p * a) pow 2 * a - (&1 + &2 * s * (x0 + p * a)) * j -
         p * j pow 2 - u = l - u + p * q0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC REAL_RING);;
