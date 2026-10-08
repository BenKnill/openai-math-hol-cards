# Card 028: Gaussian moat: the periodicity step

**Publish gate:** `028`: warm **PASS**, cold **PASS**. Cleared: every leaf reproduced cold and every control failed cold at its warm binding.

| | |
|---|---|
| Family | 028, "Uniformly bounded components of Gaussian-prime graphs." (release `CONTENTS.md`) |
| Release paper | `preprints/Bounded-Step-Walks-on-Gaussian-Primes-September-26-2026/paper.pdf`, *Bounded-Step Walks on Gaussian Primes* |
| Where | The periodicity step: a finite nonempty set is not invariant under a nonzero translation. |
| Profile | `light` |
| Leaves | `moat028_translation.ml` |
| Negative control | `negctl_moat028_empty_set_allowed.ml` |
| Release Lean | `lean/docs/028.md`; comparator config `GaussianMoat` |
| Release | github.com/openai/math at commit `adc7f124` (2026-10-06) |

## Exact statement

The kernel-checked conclusion of each headline binding, exactly as `hearth inspect --binding` printed the matched source statement (HOL Light syntax: `&n` is the real n, `!` is ∀, `/\` is ∧, `inv` is 1/x). Full inspect output: `evidence/`.

`M028_FINITE_NOT_TRANSLATION_INVARIANT`:
```
!s:(real#real)->bool a b. FINITE s /\ ~(s = {}) /\ IMAGE (\z. (FST z + a, SND z + b)) s = s ==> a = &0 /\ b = &0
```

## What HOL certifies

`M028_FINITE_NOT_TRANSLATION_INVARIANT`: a finite nonempty set of points in the plane (real pairs; ℤ² is a
special case) is not invariant under any nonzero translation. The proof is a sum argument: Σx = Σ(x+a) forces
|s|·a = 0.

## What HOL does not certify

- The theorem (a uniform bound B_D on component sizes for every step bound D); B_D is nonexplicit, and no number
  for it should be shown.
- The companion certificate "period-130 sieve, steps ≤ √2: largest island has 580 points; 486 components per
  torus". It is HOL-feasible as a certificate check but has not been done.

## Relation to the release's Lean coverage

"Lean" below means the release's selected statement, as described in its `lean/docs/NNN.md`; this repository does not rebuild or re-run that Lean.

The release's Lean covers the uniform bound on component sizes for every step bound D (B_D exists,
nonexplicit). This card is a cross-check and illustration.

## Verdicts

Control written for this repository: the same claim without the hypothesis s ≠ ∅ (false: the empty set is invariant under every translation).

Warm: Hearth on bluestar26 (hol-hearth 02443c8, HOL Light 2a1cea8), run `bluestar26:~/lanes/math-hol-cards/work/20261007T195855Z-a2c3f78`, fresh replay of every file (`--force`).

| Card | Kind | File | Warm verdict (exact first line) | Cold verdict |
|---|---|---|---|---|
| 028 | leaf | `moat028_translation.ml` | `PASSED moat028_translation.ml: 1/1 bindings proved, 0 new axioms, eval 0.5s (light)` | reproduced (135s) |
| 028 | control | `negctl_moat028_empty_set_allowed.ml` | `FAILED negctl_moat028_empty_set_allowed.ml at NEGCTL_M028_EMPTY_SET_ALLOWED (line 8): Exception: Failure "solve_goal: Too deep".` | failed at the warm binding, as designed (142s) |

Cold: Hearth's cold checker (`dev/cold-check`, hol-hearth 32862cd, which is 02443c8 plus one unrelated commit (68d79ad, Btrfs device support), run on the OrbStack Linux machine dev, image `hol-hearth-cold-checker:cards-32862cd`): HOL Light 2a1cea8 built from pinned sources in Docker with `--network none`, no Hearth runtime, CRIU or warm state. Leaves must reproduce; controls run with `--expect-failed` and must fail cold at the binding that failed warm. Run `dev:~/lanes-runs/math-hol-cards/cold/20261007T200529Z-a2c3f78 (heavy, three at a time), -light (light, one at a time) and -phase2 (the 150 receipts, the 369 retry and one 369 control, two at a time)`.

The original lane receipts (before this repository) are listed in the lane's `RESULTS.md` / `RECEIPTS.md` named under Sources.

## Sources

Math-drop lane, `~/lanes/math-drop-2026-10-07/` (Ben's machine): `hol-pilots/onscreen_light_batch.ml` (lines 97–128; split out verbatim); `scouts/hol-fast-follows.md` §5; SLATE.md HOL table. Copies and their sha256 are in `../../PROVENANCE.tsv`.
