"""Emit moser_certificate.ml from certificate.json (made by gen_certificate.py).

The HOL statements are written from the paper; certificate.json only supplies
the exact Q(sqrt3, sqrt11) normal forms that the tactics check with REAL_RING.
"""
import json
import os
import sys
from fractions import Fraction

cert = json.load(open(sys.argv[1]))
SX = int(os.environ.get("SHIFT_X", "-290"))
assert SX < 0

# Paper coordinates (angular.tex, eq. angular-seven-vectors and the uA, uB, uT display).
VERTS = [
    ("O", "&0", "&0"),
    ("A", "sqrt(&3) / &2", "&1 / &2"),
    ("B", "sqrt(&3) / &2", "--(&1 / &2)"),
    ("T", "sqrt(&3)", "&0"),
    ("UA", "(&5 * sqrt(&3) - sqrt(&11)) / &12", "(sqrt(&33) + &5) / &12"),
    ("UB", "(&5 * sqrt(&3) + sqrt(&11)) / &12", "(sqrt(&33) - &5) / &12"),
    ("UT", "&5 * sqrt(&3) / &6", "sqrt(&33) / &6"),
]
EDGES = [("O", "A"), ("O", "B"), ("A", "B"), ("T", "A"), ("T", "B"),
         ("O", "UA"), ("O", "UB"), ("UA", "UB"), ("UT", "UA"), ("UT", "UB"),
         ("T", "UT")]
IDX = {name: i for i, (name, _, _) in enumerate(VERTS)}


def lit(q):
    q = Fraction(q)
    if q.denominator == 1:
        body = f"&{abs(q.numerator)}"
    else:
        body = f"&{abs(q.numerator)} / &{q.denominator}"
    return f"--({body})" if q < 0 else f"({body})"


def nf(coeffs):
    c0, c1, c2, c3 = (Fraction(c) for c in coeffs)
    return f"`{lit(c0)} + {lit(c1)} * s + {lit(c2)} * t + {lit(c3)} * (s * t)`"


def placed(name):
    _, gx, gy = VERTS[IDX[name]]
    return f"moser_xi ({gx}) ({gy})", f"moser_ups ({gx}) ({gy})"


out = []
w = out.append
w("""(* ========================================================================= *)
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
 (`&1732050807568 / &1000000000000 < sqrt(&3) /\\
   sqrt(&3) < &1732050807569 / &1000000000000`,
  SQRT_BOUND_TAC);;

let SQRT_11_BOUNDS = prove
 (`&3316624790355 / &1000000000000 < sqrt(&11) /\\
   sqrt(&11) < &3316624790356 / &1000000000000`,
  SQRT_BOUND_TAC);;

let SQRT_33_BOUNDS = prove
 (`&5744562646538 / &1000000000000 < sqrt(&3) * sqrt(&11) /\\
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
    &0 < xi pow 2 + ups pow 2 /\\
    xi pow 2 + ups pow 2 < &4 /\\
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
      (mk_imp(`s pow 2 = &3 /\\ t pow 2 = &11`, eq)) in
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
""")

for name, gx, gy in VERTS:
    p = cert["points"][name]
    l = p["l"]
    four_minus_l = [str(4 - Fraction(l[0]))] + [str(-Fraction(c)) for c in l[1:]]
    xi, ups = placed(name)
    w(f"""let MOSER_REGION_{name} = prove
 (`three_label_region ({xi})
                      ({ups})`,
  QST_REGION_TAC
   {nf(l)}
   {nf(four_minus_l)}
   {nf(p["gap"])});;
""")

w("""(* ------------------------------------------------------------------------- *)
(* The eleven placed edges have length exactly one.                          *)
(* ------------------------------------------------------------------------- *)

let QST_EQ_TAC =
  REWRITE_TAC[moser_xi; moser_ups; SQRT_33_EQ] THEN
  MP_TAC(CONJ SQRT_3_POW_2 SQRT_11_POW_2) THEN
  SPEC_TAC(`sqrt(&11)`,`t:real`) THEN SPEC_TAC(`sqrt(&3)`,`s:real`) THEN
  CONV_TAC REAL_RING;;
""")

for a, b in EDGES:
    xa, ya = placed(a)
    xb, yb = placed(b)
    w(f"""let MOSER_EDGE_{a}_{b} = prove
 (`({xa} - {xb}) pow 2 +
   ({ya} - {yb}) pow 2 = &1`,
  QST_EQ_TAC);;
""")

w("""(* ------------------------------------------------------------------------- *)
(* The Moser graph has no proper three-colouring (vertex order O,A,B,T,uA,uB,uT).*)
(* ------------------------------------------------------------------------- *)

let MOSER_FORCED = prove
 (`!a b c d. a < 3 /\\ b < 3 /\\ c < 3 /\\ d < 3 /\\
             ~(a = b) /\\ ~(a = c) /\\ ~(b = c) /\\ ~(d = b) /\\ ~(d = c)
             ==> d = a`,
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Combined: no 3-labelling of the seven placed points avoids a monochromatic *)
(* unit pair, and all seven lie in the three-label region.                    *)
(* ------------------------------------------------------------------------- *)
""")

pts = ";\n      ".join(f"({x}, {y})" for x, y in (placed(n) for n, _, _ in VERTS))
region_conj = " /\\\n      ".join(f"three_label_region ({placed(n)[0]}) ({placed(n)[1]})" for n, _, _ in VERTS)
vx = {n: placed(n) for n, _, _ in VERTS}
w(f"""let MOSER_PLACEMENT_CERTIFICATE = prove
 (`{region_conj} /\\
   ~(?c:real#real->num.
       (!p. c p < 3) /\\
       (!x1 y1 x2 y2.
          MEM (x1,y1) [{pts}] /\\
          MEM (x2,y2) [{pts}] /\\
          (x1 - x2) pow 2 + (y1 - y2) pow 2 = &1
          ==> ~(c(x1,y1) = c(x2,y2))))`,
  REWRITE_TAC[{"; ".join(f"MOSER_REGION_{n}" for n, _, _ in VERTS)}] THEN
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
     [{"; ".join(f"MOSER_EDGE_{a}_{b}" for a, b in EDGES)}]) THEN
""")

def cpt(n):
    x, y = vx[n]
    return f"(c:real#real->num)({x},{y})"

w(f"""  SUBGOAL_THEN `{cpt("T")} = {cpt("O")}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOSER_FORCED THEN
    EXISTS_TAC `{cpt("A")}` THEN EXISTS_TAC `{cpt("B")}` THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{cpt("UT")} = {cpt("O")}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOSER_FORCED THEN
    EXISTS_TAC `{cpt("UA")}` THEN EXISTS_TAC `{cpt("UB")}` THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;
""")

sys.stdout.write("\n".join(out).replace("&290 / &250", f"&{-SX} / &250"))
