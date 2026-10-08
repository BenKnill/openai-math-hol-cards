# Card 354: Isoperimetric switches in the cubic flat three-torus (two cards)

**Publish gate:** `354-light`: warm **PASS**, cold **PASS**; `354-pi`: warm **PASS**, cold **PASS**. Cleared: every leaf reproduced cold and every control failed cold at its warm binding.

| | |
|---|---|
| Family | 354, "The isoperimetric profile of the cubic three-torus." (release `CONTENTS.md`) |
| Release paper | `preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf`, *The Isoperimetric Conjecture for the Cubic Flat Three-Torus* |
| Where | The three candidate profiles (ball, tube around a unit closed geodesic, slab) and where they cross. |
| Profile (354-light) | `light` |
| Leaves (354-light) | `torus354_light.ml` |
| Negative control (354-light) | `negctl_torus354_light_4pi_over_80.ml` |
| Profile (354-pi) | `heavy` |
| Leaves (354-pi) | `torus354_pi.ml` |
| Negative control (354-pi) | `negctl_torus354_4pi_over_80.ml` |
| Release Lean | `lean/docs/354.md`; comparator config `CubicTorus` |
| Release | github.com/openai/math at commit `adc7f124` (2026-10-06) |

## Exact statement

The kernel-checked conclusion of each headline binding, exactly as `hearth inspect --binding` printed the matched source statement (HOL Light syntax: `&n` is the real n, `!` is ∀, `/\` is ∧, `inv` is 1/x). Full inspect output: `evidence/`.

`T354_BALL_TUBE_SWITCH`:
```
!PI V b t. &0 < PI /\ &0 < V /\ &0 <= b /\ &0 <= t /\ b pow 3 = &36 * PI * V pow 2 /\ t pow 2 = &4 * PI * V ==> (b <= t <=> V <= &4 * PI / &81)
```
`T354_TUBE_SLAB_SWITCH`:
```
!PI V t. &0 < PI /\ &0 < V /\ &0 <= t /\ t pow 2 = &4 * PI * V ==> (t <= &2 <=> V <= &1 / PI)
```
`T354_SWITCH_RADII`:
```
!PI. &3 < PI ==> (&4 / &3 * PI * (&1 / &3) pow 3 = &4 * PI / &81 /\ &4 * PI * (&1 / &3) pow 2 = &4 * PI / &9 /\ PI * (&2 / &9) pow 2 = &4 * PI / &81 /\ &2 * PI * (&2 / &9) = &4 * PI / &9) /\ (PI * (&1 / PI) pow 2 = &1 / PI /\ &2 * PI * (&1 / PI) = &2) /\ &1 / &3 < &1 / &2 /\ &2 / &9 < &1 / &2 /\ &1 / PI < &1 / &2
```
`T354_PI_SWITCHES`:
```
!V r s. &0 < V /\ &0 < r /\ &0 < s /\ &4 / &3 * pi * r pow 3 = V /\ pi * s pow 2 = V ==> (&4 * pi * r pow 2 <= &2 * pi * s <=> V <= &4 * pi / &81) /\ (&2 * pi * s <= &2 <=> V <= &1 / pi)
```
`T354_PI_SWITCH_VALUES`:
```
(&4 / &3 * pi * (&1 / &3) pow 3 = &4 * pi / &81 /\ pi * (&2 / &9) pow 2 = &4 * pi / &81 /\ &4 * pi * (&1 / &3) pow 2 = &4 * pi / &9 /\ &2 * pi * (&2 / &9) = &4 * pi / &9) /\ (pi * (&1 / pi) pow 2 = &1 / pi /\ &2 * pi * (&1 / pi) = &2) /\ &4 * pi / &81 < &1 / pi /\ &1 / pi < &1 / &2 /\ &1551 / &10000 < &4 * pi / &81 /\ &4 * pi / &81 < &1552 / &10000 /\ &3183 / &10000 < &1 / pi /\ &1 / pi < &3184 / &10000 /\ &1 / &3 < &1 / &2 /\ &2 / &9 < &1 / &2
```
`T354_PI_BALL_LOSES_AT_SLAB_SWITCH`:
```
!r. &0 < r /\ &4 / &3 * pi * r pow 3 = &1 / pi ==> &2 < &4 * pi * r pow 2
```

## What HOL certifies

**Card 354-light** (`torus354_light.ml`, profile `light`). The light profile has no `pi`, so `PI` is **any**
positive real; the statements hold for every such constant, in particular for π. Candidate areas at volume V:
ball b with b³ = 36·PI·V², tube t with t² = 4·PI·V, slab 2.
- `T354_BALL_TUBE_SWITCH`: b ≤ t ⇔ V ≤ 4·PI/81.
- `T354_TUBE_SLAB_SWITCH`: t ≤ 2 ⇔ V ≤ 1/PI.
- `T354_SWITCH_RADII`: the ball radius is 1/3 and the tube radius 2/9 at 4·PI/81, both with area 4·PI/9; the
  tube radius is 1/PI with area 2 at 1/PI; for PI > 3 all radii are < 1/2, so each shape fits.

**Card 354-pi** (`torus354_pi.ml`, profile `heavy`, HOL Light's real `pi`). A ball of radius r has
V = (4/3)πr³ and area 4πr²; a tube of radius s has V = πs² and area 2πs; a slab has area 2.
- `T354_PI_SWITCHES`: for every V > 0, ball area ≤ tube area ⇔ V ≤ 4π/81, and tube area ≤ 2 ⇔ V ≤ 1/π.
- `T354_PI_SWITCH_VALUES`: at V = 4π/81 the ball radius is exactly 1/3 and the tube radius exactly 2/9, and both
  areas are 4π/9; at V = 1/π the tube radius is 1/π and its area is 2; 4π/81 < 1/π < 1/2;
  0.1551 < 4π/81 < 0.1552 and 0.3183 < 1/π < 0.3184; every radius is < 1/2, so no shape touches its own
  periodic copy.
- `T354_PI_BALL_LOSES_AT_SLAB_SWITCH`: at V = 1/π a ball would need area > 2.

Ball area cubed equals 36πV², which is the paper's (36π)^{1/3}V^{2/3}; tube area squared equals 4πV, which is
2√(πV). The proofs use only 3.1415 < π < 3.1416, which follows from HOL Light's `PI_APPROX_32`.

## What HOL does not certify

That ball, tube and slab are the minimizers. That is the theorem itself. Existence of minimizers is not covered
either.

## Relation to the release's Lean coverage

"Lean" below means the release's selected statement, as described in its `lean/docs/NNN.md`; this repository does not rebuild or re-run that Lean.

Fully covered in the release: `lean/docs/354.md` covers the full profile and all minimizers, including equality
at both transitions. We have not re-run that proof. These cards are cross-checks whose value is on screen.

## Verdicts

Card 354-pi: control from the heavy lane, the ball–tube tie claimed at V = 4π/80; `V ≤ 4π/81 ⇔ V ≤ 4π/80` is not provable. Card 354-light: control written for this repository, the same slip for generic PI (`NEGCTL_T354_BALL_TUBE_SWITCH_4PI_OVER_80`).

Warm: Hearth on bluestar26 (hol-hearth 02443c8, HOL Light 2a1cea8), run `bluestar26:~/lanes/math-hol-cards/work/20261007T195855Z-a2c3f78`, fresh replay of every file (`--force`).

| Card | Kind | File | Warm verdict (exact first line) | Cold verdict |
|---|---|---|---|---|
| 354-light | leaf | `torus354_light.ml` | `PASSED torus354_light.ml: 4/4 bindings proved, 0 new axioms, eval 0.7s (light)` | reproduced (146s) |
| 354-light | control | `negctl_torus354_light_4pi_over_80.ml` | `FAILED negctl_torus354_light_4pi_over_80.ml at NEGCTL_T354_BALL_TUBE_SWITCH_4PI_OVER_80 (line 15): Exception: Failure "REAL_ARITH '&0 < PI\n==> &0 < V\n==> &0 <= b\n==> &0 <= t\n==> b pow 3 = &36 * PI…` | failed at the warm binding, as designed (153s) |
| 354-pi | leaf | `torus354_pi.ml` | `PASSED torus354_pi.ml: 10/10 bindings proved, 0 new axioms, eval 2.7s (heavy)` | reproduced (1601s) |
| 354-pi | control | `negctl_torus354_4pi_over_80.ml` | `FAILED negctl_torus354_4pi_over_80.ml at NEGCTL_T354_PI_SWITCH_AT_4PI_OVER_80 (line 85): Exception: Failure "REAL_ARITH '&0 < V\n==> &0 < r\n==> &0 < s\n==> &4 / &3 * pi * r pow 3 = V\n==> pi * s pow …` | failed at the warm binding, as designed (1601s) |

Cold: Hearth's cold checker (`dev/cold-check`, hol-hearth 32862cd, which is 02443c8 plus one unrelated commit (68d79ad, Btrfs device support), run on the OrbStack Linux machine dev, image `hol-hearth-cold-checker:cards-32862cd`): HOL Light 2a1cea8 built from pinned sources in Docker with `--network none`, no Hearth runtime, CRIU or warm state. Leaves must reproduce; controls run with `--expect-failed` and must fail cold at the binding that failed warm. Run `dev:~/lanes-runs/math-hol-cards/cold/20261007T200529Z-a2c3f78 (heavy, three at a time), -light (light, one at a time) and -phase2 (the 150 receipts, the 369 retry and one 369 control, two at a time)`.

The original lane receipts (before this repository) are listed in the lane's `RESULTS.md` / `RECEIPTS.md` named under Sources.

## Sources

Math-drop lane, `~/lanes/math-drop-2026-10-07/` (Ben's machine): `hol-pilots/onscreen_light_batch.ml` (lines 25–95; split out verbatim), `b26-hol/torus354_pi.ml`, `b26-hol/RESULTS.md` §354; `scouts/hol-fast-follows.md` §3; SLATE.md HOL table rows 354. Copies and their sha256 are in `../../PROVENANCE.tsv`.
