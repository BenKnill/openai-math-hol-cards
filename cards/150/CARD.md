# Card 150: Triangle billiards: the corner count (counting step only)

**Publish gate:** `150`: warm **PASS**, cold **PASS**. Cleared: every leaf reproduced cold and every control failed cold at its warm binding.

| | |
|---|---|
| Family | 150, "Weak mixing of triangular billiards with an irrational angle." (release `CONTENTS.md`) |
| Release paper | `preprints/Ergodicity-of-triangular-billiards-with-an-irrational-angle-September-25-2026/Ergodicity-of-triangular-billiards-with-an-irrational-angle-September-25-2026.pdf`, *Ergodicity of triangular billiards with an irrational angle* |
| Where | Section 2: a ball entering a corner of angle α makes at most ⌈π/α⌉ bounces before it leaves (the classical unfolding argument). |
| Profile | `heavy` |
| Leaves | `billiards150_corner.ml` |
| Negative control | `negctl_billiards150_at_most_3.ml` |
| Release Lean | `lean/docs/150.md`; comparator config `IrrationalTriangleBilliard` |
| Release | github.com/openai/math at commit `adc7f124` (2026-10-06) |

## Exact statement

The kernel-checked conclusion of each headline binding, exactly as `hearth inspect --binding` printed the matched source statement (HOL Light syntax: `&n` is the real n, `!` is ∀, `/\` is ∧, `inv` is 1/x). Full inspect output: `evidence/`.

`T150_CORNER_BOUNCE_COUNT`:
```
!alpha t0 s. &0 < alpha /\ (!k. k IN s ==> t0 < &k * alpha /\ &k * alpha < t0 + pi) ==> FINITE s /\ &(CARD s) < pi / alpha + &1
```

## What HOL certifies

Only the counting step of the classical unfolding argument:
- `MULTIPLES_IN_OPEN_INTERVAL`: for α > 0, L > 0 and any real t₀, any set s of naturals with t₀ < kα < t₀ + L
  for all k ∈ s is finite, and CARD s < L/α + 1.
- `T150_CORNER_BOUNCE_COUNT` (headline): the same with L = π, so CARD s < π/α + 1, that is CARD s ≤ ⌈π/α⌉.
- `T150_ONE_RADIAN`: for α = 1, at most 4, and 4 is attained.
- `T150_POINT_THREE`: for α = 0.3, at most 11, and 11 is attained.

## What HOL does not certify

The geometric step: the unfolding; that the unfolded trajectory's polar angle sweeps an open interval of length
exactly π; and that each bounce is a crossing of a wall copy at angle kα. So HOL does **not** certify "a ball
makes at most ⌈π/α⌉ bounces"; it certifies only the counting fact the argument reduces to. The leaf header
sketches the uncertified step. Film caution (slate): don't say "mixing".

## Relation to the release's Lean coverage

"Lean" below means the release's selected statement, as described in its `lean/docs/NNN.md`; this repository does not rebuild or re-run that Lean.

Ergodicity is Lean-formalized in the release (`lean/docs/150.md`); weak mixing is paper-only ("the paper
claims"). Neither is touched by this card.

## Verdicts

Control from the heavy lane: "a one-radian corner allows at most 3", with the tactic that proves "at most 4".

Warm: Hearth on bluestar26 (hol-hearth 02443c8, HOL Light 2a1cea8), run `bluestar26:~/lanes/math-hol-cards/work/20261007T195855Z-a2c3f78`, fresh replay of every file (`--force`).

| Card | Kind | File | Warm verdict (exact first line) | Cold verdict |
|---|---|---|---|---|
| 150 | leaf | `billiards150_corner.ml` | `PASSED billiards150_corner.ml: 5/5 bindings proved, 0 new axioms, eval 1.9s (heavy)` | reproduced (2915s) |
| 150 | control | `negctl_billiards150_at_most_3.ml` | `FAILED negctl_billiards150_at_most_3.ml at NEGCTL_T150_ONE_RADIAN_AT_MOST_3 (line 96): Exception: Failure "ARITH_RULE 'CARD s < 5 ==> CARD s <= 3': REAL_ARITH '~(&0 <= real_of_int _4092265 /\\\n real_…` | failed at the warm binding, as designed (1596s) |

Cold: Hearth's cold checker (`dev/cold-check`, hol-hearth 32862cd, which is 02443c8 plus one unrelated commit (68d79ad, Btrfs device support), run on the OrbStack Linux machine dev, image `hol-hearth-cold-checker:cards-32862cd`): HOL Light 2a1cea8 built from pinned sources in Docker with `--network none`, no Hearth runtime, CRIU or warm state. Leaves must reproduce; controls run with `--expect-failed` and must fail cold at the binding that failed warm. Run `dev:~/lanes-runs/math-hol-cards/cold/20261007T200529Z-a2c3f78 (heavy, three at a time), -light (light, one at a time) and -phase2 (the 150 receipts, the 369 retry and one 369 control, two at a time)`.

The original lane receipts (before this repository) are listed in the lane's `RESULTS.md` / `RECEIPTS.md` named under Sources.

## Sources

Math-drop lane, `~/lanes/math-drop-2026-10-07/` (Ben's machine): `b26-hol/billiards150_corner.ml`, `b26-hol/RESULTS.md` §150; SLATE.md HOL table row 150. Copies and their sha256 are in `../../PROVENANCE.tsv`.
