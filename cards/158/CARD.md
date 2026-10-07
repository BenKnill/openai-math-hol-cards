# Card 158: The seven-point Moser certificate

**Publish gate:** `158`: warm **PASS**, cold **PENDING**. **Not cleared: do not advertise this card** until the gate passes.

| | |
|---|---|
| Family | 158, "The Euclidean plane cannot be colored with five colors." (release `CONTENTS.md`) |
| Release paper | `preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026/paper.pdf`, *The Euclidean plane is not five-colorable* |
| Where | `build/sections/angular.tex`: Lemma "Seven-point certificate" and Prop. "cycle cannot have length three". |
| Profile | `light` |
| Leaves | `moser_certificate.ml` |
| Negative control | `negctl_moser_certificate_shift280.ml` |
| Release Lean | `lean/docs/158.md`; comparator configs `EuclideanFiveColor` and `PlaneColoring` |
| Release | github.com/openai/math at commit `adc7f124` (2026-10-06) |

## Exact statement

The kernel-checked conclusion of each headline binding, exactly as `hearth inspect --binding` printed the matched source statement (HOL Light syntax: `&n` is the real n, `!` is ∀, `/\` is ∧, `inv` is 1/x). Full inspect output: `evidence/`.

`MOSER_PLACEMENT_CERTIFICATE`:
```
three_label_region (moser_xi (&0) (&0)) (moser_ups (&0) (&0)) /\ three_label_region (moser_xi (sqrt(&3) / &2) (&1 / &2)) (moser_ups (sqrt(&3) / &2) (&1 / &2)) /\ three_label_region (moser_xi (sqrt(&3) / &2) (--(&1 / &2))) (moser_ups (sqrt(&3) / &2) (--(&1 / &2))) /\ three_label_region (moser_xi (sqrt(&3)) (&0)) (moser_ups (sqrt(&3)) (&0)) /\ three_label_region (moser_xi ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12)) (moser_ups ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12)) /\ three_label_region (moser_xi ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12)) (moser_ups ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12)) /\ three_label_region (moser_xi (&5 * sqrt(&3) / &6) (sqrt(&33) / &6)) (moser_ups (&5 * sqrt(&3) / &6) (sqrt(&33) / &6)) /\ ~(?c:real#real->num. (!p. c p < 3) /\ (!x1 y1 x2 y2. MEM (x1,y1) [(moser_xi (&0) (&0), moser_ups (&0) (&0)); (moser_xi (sqrt(&3) / &2) (&1 / &2), moser_ups (sqrt(&3) / &2) (&1 / &2)); (moser_xi (sqrt(&3) / &2) (--(&1 / &2)), moser_ups (sqrt(&3) / &2) (--(&1 / &2))); (moser_xi (sqrt(&3)) (&0), moser_ups (sqrt(&3)) (&0)); (moser_xi ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12), moser_ups ((&5 * sqrt(&3) - sqrt(&11)) / &12) ((sqrt(&33) + &5) / &12)); (moser_xi ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12), moser_ups ((&5 * sqrt(&3) + sqrt(&11)) / &12) ((sqrt(&33) - &5) / &12)); (moser_xi (&5 * sqrt(&3) / &6) (sqrt(&33) / &6), moser_ups (&5 * sqrt(&3) / &6) (sqrt(&33) / &6))] /\ MEM (x2,y2) [(moser_xi (&0) (&0), moser_ups (&0) (&0)); (moser_xi (sqrt(&3) / &2) (&...
```

## What HOL certifies

With the paper's placement z_g = (35+12i)/37 · (g + (−290+149i)/250) of the Moser vertices
{0, A, B, T, uA, uB, uT} (A = (√3+i)/2, B = (√3−i)/2, T = √3, u = (5+i√11)/6):

1. every placed vertex satisfies 0 < l < 4 and υ²(3ξ² − υ²)² < l³(1 − l/4)(l − 1)²: the paper's
   polynomial three-label region (Lemma "Seven-point certificate");
2. the 11 placed edges have length exactly 1;
3. no labelling of the plane with 3 labels is proper on the unit pairs among these 7 placed points.

Method: each quantity is put into exact normal form a + b√3 + c√11 + d√33 (REAL_RING under
s² = 3, t² = 11), then signed by linear arithmetic from 12-digit rational bounds on √3, √11, √33.
This is a different route from both the paper and the Lean file
(`lean/OAI/Geometry/PlaneColoring/Moser.lean`), which use the paper's 4-decimal coordinate
boxes and polynomial bounds. The tightest margin is vertex B, where P′ − P ≈ 0.0007.

Foundation delta: 0 axioms, 3 definitions (`moser_xi`, `moser_ups`, `three_label_region`).
`gen/` regenerates the leaf: `gen_certificate.py` computes the exact ℚ(√3,√11) normal forms with sympy
and writes `certificate.json`; `gen_hol.py certificate.json > moser_certificate.ml`. The HOL statements are
written from the paper; the JSON only supplies the normal forms, and HOL re-proves each of them.

## What HOL does not certify

- Lemma "Polynomial three-label region": that this region really is restricted to three labels.
  That depends on the whole interface and palette argument.
- Everything else in the paper, including the main theorem (no proper five-colouring of the plane).

## Relation to the release's Lean coverage

"Lean" below means the release's selected statement, as described in its `lean/docs/NNN.md`; this repository does not rebuild or re-run that Lean.

The main theorem is formalized in Lean in the release: `lean/OAI/Geometry/PlaneColoring/` has 46 files and
about 14.7k lines, with no `sorry` found by grep, and the comparator permits only `propext`, `Quot.sound` and
`Classical.choice`. This card is an independent method for a Lean-covered step (the slate's words), not new
coverage.

Definition hole: the release's `ComparatorChallenges/EuclideanFiveColor.json` lists
`OAI.EuclideanFiveColor.ProperColoring` under `definition_names`, so the release's own comparator check compares
only that definition's name, type, universes and safety, not its body. The lead compared the two bodies by
reading: the solution's `ProperColoring k c := ∀ x y : ℂ, ‖x - y‖ = 1 → c x ≠ c y` matches the challenge's up to
the names of bound variables. The lane's Lean re-check has since confirmed this by machine (SLATE.md rule 8,
`b26-lean/RESULTS.md`; not re-run for this repository): on bluestar26, comparator run through Hearth's Lean lane
**without** `definition_names`, which makes comparator require `ProperColoring`'s body to be identical to the
challenge's, PASSED with `1/1 theorems matched` and only the standard axioms (Lean 4.34.1, Mathlib d13f23b,
comparator 46f1cef), and its Fin-6 negative control was REFUSED.

## Verdicts

Control from the lead: the placement shifted from −290 to −280. It fails at the sign step `MOSER_REGION_UT` (true gap ≈ −0.19).

Warm: Hearth on bluestar26 (hol-hearth 02443c8, HOL Light 2a1cea8), run `bluestar26:~/lanes/math-hol-cards/work/20261007T195855Z-a2c3f78`, fresh replay of every file (`--force`).

| Card | Kind | File | Warm verdict (exact first line) | Cold verdict |
|---|---|---|---|---|
| 158 | leaf | `moser_certificate.ml` | `PASSED moser_certificate.ml: 26/26 bindings proved, 0 new axioms, eval 114.0s (light)` | pending |
| 158 | control | `negctl_moser_certificate_shift280.ml` | `FAILED negctl_moser_certificate_shift280.ml at MOSER_REGION_UT (line 152): Exception: Failure "REAL_ARITH 's pow 2 = &3\n==> t pow 2 = &11\n==> &1732050807568 / &1000000000000 < s\n==> s < &1732050807…` | pending |

The original lane receipts (before this repository) are listed in the lane's `RESULTS.md` / `RECEIPTS.md` named under Sources.

## Sources

Math-drop lane, `~/lanes/math-drop-2026-10-07/` (Ben's machine): `hol-pilots/158-moser-certificate/` (`RESULTS.md`, leaf, control, generators); SLATE.md HOL table row 158. Copies and their sha256 are in `../../PROVENANCE.tsv`.
