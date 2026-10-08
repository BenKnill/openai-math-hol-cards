# Card 017: π: the n = 355 spike in the Flint–Hills series

**Publish gate:** `017`: warm **PASS**, cold **PASS**. Cleared: every leaf reproduced cold and every control failed cold at its warm binding.

| | |
|---|---|
| Family | 017, "The irrationality exponent of π is 2." (release `CONTENTS.md`) |
| Release paper | `preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf`, *The irrationality exponent of pi is 2* |
| Where | The Flint–Hills corollary's n = 355 term (the film hook). |
| Profile | `heavy` |
| Leaves | `pi355_017.ml` |
| Negative control | `negctl_pi355_017_gt25.ml` |
| Release Lean | `lean/docs/017.md`; comparator config `PiExponent` |
| Release | github.com/openai/math at commit `adc7f124` (2026-10-06) |

## Exact statement

The kernel-checked conclusion of each headline binding, exactly as `hearth inspect --binding` printed the matched source statement (HOL Light syntax: `&n` is the real n, `!` is ∀, `/\` is ∧, `inv` is 1/x). Full inspect output: `evidence/`.

`PI355_CERTIFICATE`:
```
abs(pi - &355 / &113) < &27 / &10 pow 8 /\ --(&302 / &10 pow 7) < sin(&355) /\ sin(&355) < --(&301 / &10 pow 7) /\ &245 / &10 < inv(&355 pow 3 * sin(&355) pow 2) /\ inv(&355 pow 3 * sin(&355) pow 2) < &247 / &10 /\ &24 < sum(1..355) (\n. inv(&n pow 3 * sin(&n) pow 2))
```

## What HOL certifies

Statements about HOL Light's own `pi` and `sin`, with no new definitions:
- 2.664·10⁻⁷ < 355/113 − π < 2.669·10⁻⁷, so |π − 355/113| < 2.7·10⁻⁷ (true value 2.6676·10⁻⁷);
- −3.02·10⁻⁵ < sin 355 < −3.01·10⁻⁵ (true value −3.0144·10⁻⁵);
- **24.5 < 1/(355³ sin² 355) < 24.7** (true value 24.598, the lead's float check);
- Σ_{n=1}^{355} 1/(n³ sin² n) > 24, because every term is ≥ 0.

The proof uses sin 355 = −sin(355 − 113π) (from `SIN_ADD`, `SIN_NPI`, `COS_NPI`), then
y − y³/2 ≤ sin y ≤ |y| for the small y = 355 − 113π > 0 (`TAYLOR_CSIN` with n = 0, `REAL_ABS_SIN_BOUND_LE`).
The only π input is HOL's `PI_APPROX_32`: |π − 13493037705/2³²| ≤ 2⁻³² (`Multivariate/transcendentals.ml`).

## What HOL does not certify

- That the Flint–Hills series converges. That is the paper's corollary and is paper-only ("the paper claims").
- Anything about the irrationality exponent.
- The partial sum through n = 354 (≈ 4.807). That would need a lower bound on |sin n| for every n ≤ 354.

## Relation to the release's Lean coverage

"Lean" below means the release's selected statement, as described in its `lean/docs/NNN.md`; this repository does not rebuild or re-run that Lean.

`lean/docs/017.md` covers μ(π) = 2 and states that Flint–Hills is outside its selected statement. Trace caution
(honesty rule 4): if this card is used in a "how a machine found it" film, the reasoning traces are mostly a
summarizer's narration; only the boxed excerpts are verbatim.

## Verdicts

Control from the heavy lane: the term claimed > 25 with the tactic that proves > 24.5.

Warm: Hearth on bluestar26 (hol-hearth 02443c8, HOL Light 2a1cea8), run `bluestar26:~/lanes/math-hol-cards/work/20261007T195855Z-a2c3f78`, fresh replay of every file (`--force`).

| Card | Kind | File | Warm verdict (exact first line) | Cold verdict |
|---|---|---|---|---|
| 017 | leaf | `pi355_017.ml` | `PASSED pi355_017.ml: 8/8 bindings proved, 0 new axioms, eval 2.1s (heavy)` | reproduced (1601s) |
| 017 | control | `negctl_pi355_017_gt25.ml` | `FAILED negctl_pi355_017_gt25.ml at NEGCTL_FLINT_HILLS_355_TERM_GT_25 (line 50): Exception: Failure "REAL_ARITH 's pow 2 < &22801 / &25000000000000 /\\\n&90601 / &100000000000000 < s pow 2 /\\\ns < -- …` | failed at the warm binding, as designed (1485s) |

Cold: Hearth's cold checker (`dev/cold-check`, hol-hearth 32862cd, which is 02443c8 plus one unrelated commit (68d79ad, Btrfs device support), run on the OrbStack Linux machine dev, image `hol-hearth-cold-checker:cards-32862cd`): HOL Light 2a1cea8 built from pinned sources in Docker with `--network none`, no Hearth runtime, CRIU or warm state. Leaves must reproduce; controls run with `--expect-failed` and must fail cold at the binding that failed warm. Run `dev:~/lanes-runs/math-hol-cards/cold/20261007T200529Z-a2c3f78 (heavy, three at a time), -light (light, one at a time) and -phase2 (the 150 receipts, the 369 retry and one 369 control, two at a time)`.

The original lane receipts (before this repository) are listed in the lane's `RESULTS.md` / `RECEIPTS.md` named under Sources.

## Sources

Math-drop lane, `~/lanes/math-drop-2026-10-07/` (Ben's machine): `b26-hol/pi355_017.ml`, `b26-hol/RESULTS.md` §017; SLATE.md HOL table row 017. Copies and their sha256 are in `../../PROVENANCE.tsv`.
