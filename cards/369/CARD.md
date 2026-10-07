# Card 369: Hot spots on the disk: the zero of J₁′ (three leaves)

**Publish gate:** `369`: warm **PASS**, cold **PENDING**. **Not cleared: do not advertise this card** until the gate passes.

| | |
|---|---|
| Family | 369, "The hot spots conjecture for simply connected planar domains." (release `CONTENTS.md`) |
| Release paper | `preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf`, *Strict hot spots and absence of interior critical points on smooth simply connected planar domains* |
| Where | The disk example: the first Neumann mode's edge sits at the zero j′₁,₁ ≈ 1.84118 of J₁′. |
| Profile | `heavy` |
| Leaves | `hotspots369_bessel.ml`, `hotspots369_bessel_root.ml`, `hotspots369_bessel_deriv.ml` |
| Negative control | `negctl_hotspots369_pos_at_18412.ml`, `negctl_hotspots369_root_shifted.ml`, `negctl_hotspots369_deriv_is_j0.ml` |
| Release Lean | `lean/docs/369.md`; comparator config `HotSpots` |
| Release | github.com/openai/math at commit `adc7f124` (2026-10-06) |

## Exact statement

The kernel-checked conclusion of each headline binding, exactly as `hearth inspect --binding` printed the matched source statement (HOL Light syntax: `&n` is the real n, `!` is ∀, `/\` is ∧, `inv` is 1/x). Full inspect output: `evidence/`.

`HOTSPOT369_J1_CRITICAL_POINT`:
```
(!x. &1 < x /\ x < &2 ==> (bessel_j1 has_real_derivative bessel_dj1 x) (atreal x)) /\ &0 < bessel_dj1(&18411 / &10000) /\ bessel_dj1(&18412 / &10000) < &0 /\ (?x. &18411 / &10000 < x /\ x < &18412 / &10000 /\ (bessel_j1 has_real_derivative &0) (atreal x))
```
`HOTSPOT369_ROOT`:
```
bessel_dj1 real_continuous_on real_interval[&1,&2] /\ &0 < bessel_dj1(&18411 / &10000) /\ bessel_dj1(&18412 / &10000) < &0 /\ (?x. &18411 / &10000 < x /\ x < &18412 / &10000 /\ bessel_dj1 x = &0)
```
`HOTSPOT369_SIGN_CHANGE`:
```
&0 < bessel_dj1(&18411 / &10000) /\ bessel_dj1(&18412 / &10000) < &0
```

## What HOL certifies

**Read the definitions first.** All three leaves make the same six `new_definition`s and no axioms: the
standard power series (DLMF 10.2.2) `bessel_j0 x` = Σ_k (−1)^k (x²/4)^k / (k!)², `bessel_j1 x` =
Σ_k (−1)^k (x/2)(x²/4)^k / (k!(k+1)!), and `bessel_dj1 x` = `bessel_j0 x − bessel_j1 x / x` (J₁′ by the
recurrence, DLMF 10.6.2), each sum HOL's `real_infsum (from 0)`, plus the three term functions.

- `hotspots369_bessel.ml` (16 bindings), `HOTSPOT369_SIGN_CHANGE`: both series converge for |x| ≤ 2; the
  termwise series for `bessel_dj1`; alternating-series bounds; J₁′(1.8411) > 0 > J₁′(1.8412) from exact
  rational partial sums through k = 5 (+3.37·10⁻⁵) and k = 6 (−6.64·10⁻⁶).
- `hotspots369_bessel_root.ml` (24 bindings, standalone), `HOTSPOT369_ROOT`: `bessel_dj1` is continuous on
  [1, 2] (Weierstrass M-test), and by the intermediate value theorem there is some x with 1.8411 < x < 1.8412
  and J₁′(x) = 0.
- `hotspots369_bessel_deriv.ml` (27 bindings, standalone; the headline), `HOTSPOT369_J1_CRITICAL_POINT`: on
  (1, 2) the J₁ series is differentiable with derivative `bessel_dj1` (= J₀ − J₁/x), and that derivative is zero
  at some x with 1.8411 < x < 1.8412.

## What HOL does not certify

- That these series are "the" Bessel functions. They are the standard definitions, but HOL has no Bessel library.
- In the first two leaves, that `bessel_dj1` is the derivative of `bessel_j1`; there J₁′ is *defined* as
  J₀ − J₁/x. The third leaf proves it, on (1, 2) only.
- That this zero is the *first* positive zero of J₁′, or the only one in the bracket.
- Anything about the Neumann problem on the disk or the hot-spots theorem.

## Relation to the release's Lean coverage

"Lean" below means the release's selected statement, as described in its `lean/docs/NNN.md`; this repository does not rebuild or re-run that Lean.

The theorem is Lean-formalized in the release (`lean/docs/369.md`; the slate: it matches the paper, including
multiplicity). This card is an on-screen illustration.

## Verdicts

Three controls from the heavy lane: J₁′(1.8412) > 0 (one step right); a zero claimed in (1.8412, 1.8413); and the slip "J₁′ = J₀" at the level of terms (fails at k = 0, 1/2 ≠ 1).

Warm: Hearth on bluestar26 (hol-hearth 02443c8, HOL Light 2a1cea8), run `bluestar26:~/lanes/math-hol-cards/work/20261007T195855Z-a2c3f78`, fresh replay of every file (`--force`).

| Card | Kind | File | Warm verdict (exact first line) | Cold verdict |
|---|---|---|---|---|
| 369 | leaf | `hotspots369_bessel.ml` | `PASSED hotspots369_bessel.ml: 16/16 bindings proved, 0 new axioms, eval 6.4s (heavy)` | pending |
| 369 | leaf | `hotspots369_bessel_root.ml` | `PASSED hotspots369_bessel_root.ml: 24/24 bindings proved, 0 new axioms, eval 8.6s (heavy)` | pending |
| 369 | leaf | `hotspots369_bessel_deriv.ml` | `PASSED hotspots369_bessel_deriv.ml: 27/27 bindings proved, 0 new axioms, eval 7.6s (heavy)` | pending |
| 369 | control | `negctl_hotspots369_pos_at_18412.ml` | `FAILED negctl_hotspots369_pos_at_18412.ml at NEGCTL_BESSEL_DJ1_POS_AT_18412 (line 255): Exception: Failure "TAC_PROOF: Unsolved goals".` | pending |
| 369 | control | `negctl_hotspots369_root_shifted.ml` | `FAILED negctl_hotspots369_root_shifted.ml at NEGCTL_BESSEL_DJ1_ROOT_SHIFTED (line 388): Exception: Failure "MATCH_MP_TAC: No match".` | pending |
| 369 | control | `negctl_hotspots369_deriv_is_j0.ml` | `FAILED negctl_hotspots369_deriv_is_j0.ml at NEGCTL_BESSEL_J1_TERM_DERIV_IS_J0 (line 347): Exception: Failure "REAL_ARITH '&1 *\n((x * inv (&2)) * &0 * inv (&1) * inv (&1) +\n (&1 * inv (&2)) * &1 * in…` | pending |

The original lane receipts (before this repository) are listed in the lane's `RESULTS.md` / `RECEIPTS.md` named under Sources.

## Sources

Math-drop lane, `~/lanes/math-drop-2026-10-07/` (Ben's machine): `b26-hol/hotspots369_*.ml`, `b26-hol/RESULTS.md` §369; SLATE.md HOL table row 369. Copies and their sha256 are in `../../PROVENANCE.tsv`.
