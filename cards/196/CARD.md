# Card 196: Kaplansky zero divisors: the paper's two load-bearing rationals

**Publish gate:** `196`: warm **PASS**, cold **PENDING**. **Not cleared: do not advertise this card** until the gate passes.

| | |
|---|---|
| Family | 196, "A counterexample to Kaplansky’s zero-divisor conjecture." (release `CONTENTS.md`) |
| Release paper | `preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf`, *A Torsion-Free Group Algebra with Zero Divisors* |
| Where | `build/sections/types.tex`, lines 81–91. |
| Profile | `light` |
| Leaves | `kaplansky196_bounds.ml` |
| Negative control | `negctl_kaplansky196_below_99_100.ml` |
| Release Lean | `lean/docs/196.md`; comparator config `TorsionFreeZeroDivisors` |
| Release | github.com/openai/math at commit `adc7f124` (2026-10-06) |

## Exact statement

The kernel-checked conclusion of each headline binding, exactly as `hearth inspect --binding` printed the matched source statement (HOL Light syntax: `&n` is the real n, `!` is ∀, `/\` is ∧, `inv` is 1/x). Full inspect output: `evidence/`.

`K196_RATIONAL_BOUNDS`:
```
let q = &128 and v = &16513 and p = &129 / &16513 in q / (q + &1) + &3 * p pow 2 + &12 / (q + &1) pow 2 = &500731261911 / &504183783481 /\ &500731261911 / &504183783481 < &149 / &150 /\ (&2 + v * p pow 2 + &12 * p pow 2) / &5 = &820350863 / &1363395845 /\ &820350863 / &1363395845 < &149 / &150
```

## What HOL certifies

With q = 128, v = 16513 and p = 129/16513:
- q/(q+1) + 3p² + 12/(q+1)² = 500731261911/504183783481 < 149/150;
- (2 + vp² + 12p²)/5 = 820350863/1363395845 < 149/150.

HOL checks both equalities and both inequalities.

## What HOL does not certify

Only the arithmetic is covered. The bounds on (Mf)(t) that these numbers feed are the paper's, and so is the
probabilistic construction (there is no explicit group to show).

## Relation to the release's Lean coverage

"Lean" below means the release's selected statement, as described in its `lean/docs/NNN.md`; this repository does not rebuild or re-run that Lean.

The release's Lean covers the full counterexample (α, β ≠ 0 with αβ = 0 in F₂[G]). This card is a trivial
cross-check; these are the exact numbers a film would show.

## Verdicts

Control written for this repository: the first bound claimed below 99/100 instead of 149/150 (the value is 0.99315…).

Warm: Hearth on bluestar26 (hol-hearth 02443c8, HOL Light 2a1cea8), run `bluestar26:~/lanes/math-hol-cards/work/20261007T195855Z-a2c3f78`, fresh replay of every file (`--force`).

| Card | Kind | File | Warm verdict (exact first line) | Cold verdict |
|---|---|---|---|---|
| 196 | leaf | `kaplansky196_bounds.ml` | `PASSED kaplansky196_bounds.ml: 1/1 bindings proved, 0 new axioms, eval 0.5s (light)` | pending |
| 196 | control | `negctl_kaplansky196_below_99_100.ml` | `FAILED negctl_kaplansky196_below_99_100.ml at NEGCTL_K196_FIRST_BOUND_BELOW_99_100 (line 8): Exception: Failure "TAC_PROOF: Unsolved goals".` | pending |

The original lane receipts (before this repository) are listed in the lane's `RESULTS.md` / `RECEIPTS.md` named under Sources.

## Sources

Math-drop lane, `~/lanes/math-drop-2026-10-07/` (Ben's machine): `hol-pilots/onscreen_light_batch.ml` (lines 7–23; split out verbatim); `scouts/hol-fast-follows.md` §4; SLATE.md HOL table. Copies and their sha256 are in `../../PROVENANCE.tsv`.
