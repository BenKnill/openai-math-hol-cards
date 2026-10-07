# Card 353: Dimension-ten affine maximal graph: the algebra of the invariant box

**Publish gate:** `353`: warm **PASS**, cold **PENDING**. **Not cleared: do not advertise this card** until the gate passes.

| | |
|---|---|
| Family | 353, "Affine Bernstein rigidity through dimension nine and a smooth dimension-ten counterexample." (release `CONTENTS.md`) |
| Release paper | `preprints/Smooth-Nonquadratic-Affine-Maximal-Graph-in-Dimension-Ten-October-5-2026/affine-maximal-dimension-ten.pdf`, *A Smooth Nonquadratic Entire Affine Maximal Graph in Dimension Ten* |
| Where | `build/source/main.tex`, Section 4, Lemmas 4.1 and 4.2. |
| Profile | `light` |
| Leaves | `affine_box_353.ml` |
| Negative control | `negctl_affine_box_353_corner_shifted.ml` |
| Release Lean | `lean/docs/353.md`; comparator config `AffineBernstein` |
| Release | github.com/openai/math at commit `adc7f124` (2026-10-06) |

## Exact statement

The kernel-checked conclusion of each headline binding, exactly as `hearth inspect --binding` printed the matched source statement (HOL Light syntax: `&n` is the real n, `!` is ∀, `/\` is ∧, `inv` is 1/x). Full inspect output: `evidence/`.

`AB353_D_EQUATION`:
```
!m k g a b c ad bd cd. ~(b = &0) /\ ad = a * (&1 + b - a) /\ bd = b * (m + a + g * c - m * b) /\ cd = c * (&1 + c - (m - &1) * b) + k * a * b ==> (cd * b - c * bd) / b pow 2 = (k - c / b) * a - (m - &1) * (c / b) + b * (c / b) * (&1 + (&1 - g) * (c / b))
```
`AB353_CORNER_STATIONARY`:
```
let a = &9 / &2 and b = &7 / &2 and d = &33 / &7 in a * (&1 + b - a) = &0 /\ b * (&9 + a + (&12 / &11) * b * d - &9 * b) = &0 /\ (&11 - d) * a - &8 * d + b * d * (&1 - d / &11) = &0
```
`AB353_CROSS_PARTIALS_NONNEG`:
```
!a b d. &0 <= a /\ a <= &9 / &2 /\ &0 <= b /\ b <= &7 / &2 /\ &0 <= d /\ d <= &33 / &7 ==> &0 <= a /\ &0 <= b /\ &0 <= (&12 / &11) * b pow 2 /\ &0 <= &11 - d /\ &0 <= d * (&1 - d / &11)
```
`AB353_FACE_SIGNS`:
```
!a b d. &0 <= a /\ a <= &9 / &2 /\ &0 <= b /\ b <= &7 / &2 /\ &0 <= d /\ d <= &33 / &7 ==> (a = &9 / &2 ==> a * (&1 + b - a) <= &0) /\ (b = &7 / &2 ==> b * (&9 + a + (&12 / &11) * b * d - &9 * b) <= &0) /\ (d = &33 / &7 ==> (&11 - d) * a - &8 * d + b * d * (&1 - d / &11) <= &0) /\ (a = &0 ==> a * (&1 + b - a) = &0) /\ (b = &0 ==> b * (&9 + a + (&12 / &11) * b * d - &9 * b) = &0) /\ (d = &0 ==> &0 <= (&11 - d) * a - &8 * d + b * d * (&1 - d / &11))
```

## What HOL certifies

The finite algebraic kernel of the invariant box B = [0, 9/2] × [0, 7/2] × [0, 33/7] for the autonomous system
(m = 9, k = 11, γ = 12/11)

    A' = A (1 + B − A),  B' = B (9 + A + (12/11) B D − 9 B),  D' = (11 − D) A − 8 D + B D (1 − D/11):

- `AB353_D_EQUATION`: the D-equation follows from the paper's C-equation with D = C/B, for general m, k, γ;
- `AB353_CORNER_STATIONARY`: the upper corner (9/2, 7/2, 33/7) is a stationary point;
- `AB353_CROSS_PARTIALS_NONNEG`: the cross-partials the paper lists are ≥ 0 on the box;
- `AB353_FACE_SIGNS`: the sign of the outward (or inward) component on each of the six faces.

## What HOL does not certify

The ODE derivation of the A, B, C equations from the radial system; the invariance argument itself (projection
plus Gronwall); the local solution at r = 0; Proposition 2.1 (the reduction of the fourth-order PDE); and
smoothness and positivity of the resulting u on ℝ¹⁰. The paper claims all of these. In short, the ODE and PDE
reduction are not covered.

## Relation to the release's Lean coverage

"Lean" below means the release's selected statement, as described in its `lean/docs/NNN.md`; this repository does not rebuild or re-run that Lean.

`lean/docs/353.md` covers only the companion "affine Bernstein in dimensions 3–9". The dimension-ten
counterexample is paper-only in the release; this card checks a finite algebraic piece of it.

## Verdicts

Control written for this repository (the lane had none): the stationary corner claimed at (9/2, 7/2, 34/7), with the leaf's tactic. It fails because the B- and D-components are nonzero there.

Warm: Hearth on bluestar26 (hol-hearth 02443c8, HOL Light 2a1cea8), run `bluestar26:~/lanes/math-hol-cards/work/20261007T195855Z-a2c3f78`, fresh replay of every file (`--force`).

| Card | Kind | File | Warm verdict (exact first line) | Cold verdict |
|---|---|---|---|---|
| 353 | leaf | `affine_box_353.ml` | `PASSED affine_box_353.ml: 4/4 bindings proved, 0 new axioms, eval 0.8s (light)` | pending |
| 353 | control | `negctl_affine_box_353_corner_shifted.ml` | `FAILED negctl_affine_box_353_corner_shifted.ml at NEGCTL_AB353_CORNER_D_34_7 (line 8): Exception: Failure "TAC_PROOF: Unsolved goals".` | pending |

The original lane receipts (before this repository) are listed in the lane's `RESULTS.md` / `RECEIPTS.md` named under Sources.

## Sources

Math-drop lane, `~/lanes/math-drop-2026-10-07/` (Ben's machine): `hol-pilots/affine_box_353.ml` and `RECEIPTS.md`; `scouts/hol-fast-follows.md` §2; SLATE.md HOL table row 353. Copies and their sha256 are in `../../PROVENANCE.tsv`.
