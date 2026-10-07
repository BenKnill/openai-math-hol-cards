# Card 325: Complete Crouzeix: the sharpness arithmetic, real form

**Publish gate:** `325`: warm **PASS**, cold **PENDING**. **Not cleared: do not advertise this card** until the gate passes.

| | |
|---|---|
| Family | 325, "The complete Crouzeix conjecture." (release `CONTENTS.md`) |
| Release paper | `preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf`, *The complete Crouzeix theorem: optimal similarity and a common positive boundary representation* |
| Also in | `preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/paper.pdf`, *A direct proof of the complete Crouzeix inequality* |
| Where | The sharpness example (n = 2, m = 1, P(z) = z, A = [[0,2],[0,0]]: \|x*Ax\| = 2\|x₁x₂\| ≤ 1 for unit x). It appears in both papers (`build/main.tex` line 1159 of the first, line 526 of the second); the leaf does not say which one it was written from. |
| Profile | `light` |
| Leaves | `crouzeix325_two_xy.ml` |
| Negative control | `negctl_crouzeix325_half.ml` |
| Release Lean | `lean/docs/325.md`; comparator configs `CompleteCrouzeix`, `CrouzeixHilbert`, `DirectCrouzeix`, `HilbertCrouzeix`, `StructuralCrouzeix` |
| Release | github.com/openai/math at commit `adc7f124` (2026-10-06) |

## Exact statement

The kernel-checked conclusion of each headline binding, exactly as `hearth inspect --binding` printed the matched source statement (HOL Light syntax: `&n` is the real n, `!` is ∀, `/\` is ∧, `inv` is 1/x). Full inspect output: `evidence/`.

`C325_TWO_XY`:
```
!x y. x pow 2 + y pow 2 = &1 ==> abs(&2 * x * y) <= &1
```

## What HOL certifies

`C325_TWO_XY`: if x² + y² = 1 then |2xy| ≤ 1. With x = |a| and y = |b| this is the paper's |2 conj(a) b| ≤ 1
when |a|² + |b|² = 1.

## What HOL does not certify

- The complex-modulus step |conj a| = |a|, which needs complex numbers; the `light` profile does not load them.
- The theorem itself and the rest of the sharpness argument.

## Relation to the release's Lean coverage

"Lean" below means the release's selected statement, as described in its `lean/docs/NNN.md`; this repository does not rebuild or re-run that Lean.

The release's Lean covers it. This card is a trivial cross-check whose value is on screen. Provenance caution
(honesty rule 5): 325 has other 2026 proofs.

## Verdicts

Control written for this repository: |2xy| ≤ 1/2 claimed instead (false at x = y = 1/√2).

Warm: Hearth on bluestar26 (hol-hearth 02443c8, HOL Light 2a1cea8), run `bluestar26:~/lanes/math-hol-cards/work/20261007T195855Z-a2c3f78`, fresh replay of every file (`--force`).

| Card | Kind | File | Warm verdict (exact first line) | Cold verdict |
|---|---|---|---|---|
| 325 | leaf | `crouzeix325_two_xy.ml` | `PASSED crouzeix325_two_xy.ml: 1/1 bindings proved, 0 new axioms, eval 0.4s (light)` | pending |
| 325 | control | `negctl_crouzeix325_half.ml` | `FAILED negctl_crouzeix325_half.ml at NEGCTL_C325_TWO_XY_HALF (line 8): Exception: Failure "MATCH_MP_TAC: No match".` | pending |

The original lane receipts (before this repository) are listed in the lane's `RESULTS.md` / `RECEIPTS.md` named under Sources.

## Sources

Math-drop lane, `~/lanes/math-drop-2026-10-07/` (Ben's machine): `hol-pilots/onscreen_light_batch.ml` (lines 130–145; split out verbatim); `scouts/hol-fast-follows.md` ("also considered"); SLATE.md HOL table. Copies and their sha256 are in `../../PROVENANCE.tsv`.
