# openai-math HOL Light cards

Twelve small HOL Light proof cards associated with **eleven families** in the [OpenAI math release](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a). Family 354 has two cards. Each card includes the proof source, a precise account of what is certified, and at least one negative control.

The collection combines independent checks of selected steps with illustrative calculations for short math films. A card's relationship to the release's Lean formalization is stated in its `CARD.md`. None proves a headline theorem of the release. In particular, the Flint–Hills calculation in 017 and the disk-series calculation in 369 are supporting illustrations; they are not claimed to reproduce the release's selected Lean statements.

**Recorded proof status, 2026-10-08:** all twelve cards have successful warm and cold evidence. The complete set comprises **15 positive proof leaves and 14 negative-control files**. All 29 final cold results are present. The earlier memory-killed attempt for one 369 leaf remains in the record, together with its successful retry. These are retained execution records, not executions performed by opening this repository.

The proof leaves and profile recipes are plain HOL Light source. The original Hearth orchestration is private. The public convenience runner and manual loading instructions are below; neither should be confused with a statement-and-axiom checker.

**Coverage update, 2026-10-08:** the original release comparisons are pinned to `adc7f124`. Upstream [`fd4aeeb2`](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb) now includes the October 5 stable-coordinate result in Lean. The 049 row and [card update](cards/049/CARD.md#coverage-update--2026-10-08) reflect that source change. This is a coverage update, not a new proof replay.

## Cards

| Card | Family | What HOL certifies | Relation to the release's Lean | Profile | Warm | Cold |
|---|---|---|---|---|---|---|
| [158](cards/158/CARD.md) | 158 · The Euclidean plane cannot be colored with five colors | The seven placed Moser vertices lie in the three-label region, the 11 edges have length exactly 1, and no proper 3-labelling exists; exact arithmetic in ℚ(√3,√11) | Independent method for a Lean-covered step | `light` | PASS (26/26) | PASS |
| [049](cards/049/CARD.md) | 049 · A stable-coordinate counterexample in four variables | Two explicit polynomial maps on ℝ⁵ are mutually inverse and send the paper's f to the first coordinate | Independent polynomial-identity check; upstream fd4aeeb2 now also covers the October 5 stable-coordinate result. This HOL card does not prove its noncoordinate obstruction | `light` | PASS (8/8; 30/30) | PASS |
| [353](cards/353/CARD.md) | 353 · Affine Bernstein rigidity through dimension nine and a smooth dimension-ten counterexample | The algebra of the invariant box: stationary corner (9/2, 7/2, 33/7), face signs, the D-equation from the C-equation | Checks algebra inside a result that is paper-only in the release (Lean covers dimensions 3–9 only); the ODE and PDE reduction are not covered | `light` | PASS (4/4) | PASS |
| [354-light](cards/354/CARD.md) | 354 · The isoperimetric profile of the cubic three-torus | Switch volumes 4·PI/81 and 1/PI and the radii there, for any positive constant PI | Cross-check of a Lean-covered result; on-screen value | `light` | PASS (4/4) | PASS |
| [354-pi](cards/354/CARD.md) | 354 · The isoperimetric profile of the cubic three-torus | The same with HOL's real π: ties at 4π/81 (radii 1/3, 2/9) and at 1/π (area 2); the ball loses at 1/π | Cross-check; minimality is Lean's | `heavy` | PASS (10/10) | PASS |
| [196](cards/196/CARD.md) | 196 · A counterexample to Kaplansky’s zero-divisor conjecture | The paper's two exact rationals and both bounds < 149/150 | Cross-check of a Lean-covered result; on-screen value | `light` | PASS (1/1) | PASS |
| [028](cards/028/CARD.md) | 028 · Uniformly bounded components of Gaussian-prime graphs | A finite nonempty set in the plane is not invariant under a nonzero translation | Cross-check of a Lean-covered result; on-screen value | `light` | PASS (1/1) | PASS |
| [325](cards/325/CARD.md) | 325 · The complete Crouzeix conjecture | x² + y² = 1 ⇒ \|2xy\| ≤ 1 (real form of the sharpness case) | Cross-check of a Lean-covered result; on-screen value | `light` | PASS (1/1) | PASS |
| [017](cards/017/CARD.md) | 017 · The irrationality exponent of π is 2 | 2.664·10⁻⁷ < 355/113 − π < 2.669·10⁻⁷ and 24.5 < 1/(355³ sin² 355) < 24.7, so the Flint–Hills partial sum through n = 355 exceeds 24 | Hook card; Flint–Hills convergence stays paper-only | `heavy` | PASS (8/8) | PASS |
| [188](cards/188/CARD.md) | 188 · The sharp terminal leave in random triangle removal | q = (1+2Dt)^(−1/2) solves q′ = −Dq³ with q(0) = 1, and the leave constant tends to 1/(2√2) | The heuristic's arithmetic only; nothing about the random process | `heavy` | PASS (7/7) | PASS |
| [369](cards/369/CARD.md) | 369 · The hot spots conjecture for simply connected planar domains | The J₁ power series has derivative J₀ − J₁/x on (1, 2), and that derivative vanishes somewhere in (1.8411, 1.8412) | Illustration; not that this is the first zero, nor that the series are "the" Bessel functions | `heavy` | PASS (16/16; 24/24; 27/27) | PASS |
| [150](cards/150/CARD.md) | 150 · Weak mixing of triangular billiards with an irrational angle | Counting step only: at most ⌈π/α⌉ multiples of α fit in an open interval of length π | Not the bounce claim; the unfolding geometry is not certified | `heavy` | PASS (5/5) | PASS |


The warm evidence reports 172 proved bindings across the 15 positive leaves, with no new axioms. Warm runs used hol-hearth `02443c8` and HOL Light `2a1cea8f1cb7f3885a60d947ba06eabac6ec1d32`. The retained cold checks rebuilt pinned HOL Light sources in Docker without warm state or a Hearth runtime. Each positive receipt reproduced; each negative control failed at the binding recorded in its warm receipt.

Evidence: `evidence/warm/`, `evidence/cold/cold.tsv` and `evidence/cold/verdicts/`. The cold table retains 30 attempts for 29 distinct files because one attempt exited after HOL was killed for memory. A failed attempt is not counted as a successful receipt.

Cards 196, 028, 325 and 354-light originated as one batch file and were split into family leaves. Their controls, and 353's control, were added for this repository. `PROVENANCE.tsv` records the original copies and their hashes; subsequent reviewed changes are recorded in git.

## Claim boundaries

1. A HOL certificate establishes its actual formal statement under its definitions and imported library. Its connection to the paper is a separate, visible interpretation in the card.
2. Refer to the release's `lean/docs/NNN.md` for its selected Lean statements. A paper title does not describe the full scope of a formalization.
3. For unformalized paper conclusions, use “the paper claims.” Do not describe this collection as establishing the papers' main theorems or as the first proof of any result.
4. The example for family 049 checks the October 5 paper’s explicit polynomial inverse maps on ℝ⁵; it does not establish the non-coordinate claim for that paper’s particular polynomial. Both the September 24 companion and, as of upstream `fd4aeeb2`, the October 5 stable-coordinate result have selected Lean coverage, as explained in the card. Family 353 checks dimension-10 invariant-box algebra, not the full counterexample or its ODE/PDE argument.
5. A deliberately failing control is evidence about the tested check, not proof that a verifier rejects every invalid input.
6. HOL replay and the separate Lean re-check are distinct activities. The updated Lean results and their exact limits are in [Comparator re-check](docs/comparator-recheck.md).
7. This work used AI assistance. The archived scout notes are [historical context](docs/history/scout-rules-20261008-0103Z.md), not current status.

## Comparator re-check

At release commit `adc7f124`, the separate Lean lane checked 18 release configurations plus an additional Fin-6 negative control: **15 strict passes**, **two strict refusals with supported benign explanations**, and an ElementaryPositivity pass using its original release configuration. The two refused cases also passed their original configurations. Their strict verdicts remain REFUSED.

The configuration observation concerns the documented treatment of `definition_names` as holes whose bodies are not compared. We found no substantive definition change in the cases inspected. The supplementary diagnostic does not reproduce comparator's complete exported dependency walk, and the results do not establish all 405 configurations or the correspondence between every formal statement and its informal problem. See the [full dated note](docs/comparator-recheck.md) for counts, source links and limitations.

## Reproduce with plain HOL Light

Use HOL Light commit `2a1cea8f1cb7f3885a60d947ba06eabac6ec1d32`. The recorded cold builds used OCaml 5.3.0 and camlp5 8.03.01. Follow the pinned HOL Light checkout's build instructions.

```sh
git clone https://github.com/jrh13/hol-light
cd hol-light
git checkout 2a1cea8f1cb7f3885a60d947ba06eabac6ec1d32
make
cd /path/to/openai-math-hol-cards
HOLDIR=/path/to/hol-light bin/replay-plain out/plain-196 196
```

`bin/replay-plain` uses Python 3 standard-library modules. It starts a fresh HOL process for each source file, checks process and loading errors, requires completion markers, and checks recognized theorem bindings have type `thm`. Controls must raise a HOL `Failure` during source loading, after a clean profile load. Failed or incomplete execution gives a failing exit status.

It is a convenience replay runner. It does not compare theorem statements against independent specifications, audit axioms, issue Hearth receipts, or establish the specific failing control binding. Review the source statements directly and use the retained cold evidence for the stronger recorded checks.

The historical plain-run summaries report seven light cards and card 017. Their raw HOL logs were not included in the review packet, and those runs used an earlier, weaker wrapper. They are not independent validation of this revised wrapper or evidence that all twelve cards have completed this public replay route. Publication checks of the revised runner are recorded separately.

| Profile | Recipe | Cards |
|---|---|---|
| light | `replay/light.ml`: `calc_rat.ml`, real prioritization, ring theory and the REAL_RING tactic binding | 158, 049, 353, 354-light, 196, 028, 325 |
| heavy | `replay/heavy.ml`: the light prerequisites plus `Multivariate/realanalysis.ml` | 354-pi, 017, 188, 369, 150 |

Loading the heavy profile from scratch can take substantial time. Its historical 017 convenience run took about 110 minutes. Begin with a light card.

To inspect a proof directly in `hol.sh`:

```ocaml
loadt "/path/to/openai-math-hol-cards/replay/light.ml";;
loadt "/path/to/openai-math-hol-cards/cards/196/kaplansky196_bounds.ml";;
K196_RATIONAL_BOUNDS;;
```

## Reproduce using the original Hearth setup

Hearth is currently private; these commands are for people who already have access to a configured runtime. They are included to explain how the retained evidence was obtained, not as a public dependency.

```sh
hearth prove cards/196/kaplansky196_bounds.ml --profile light --run-root out/runs-196 --force
HEARTH_BIN=hearth bin/run-cards out/warm-1
```

In the matching hol-hearth checkout, build its cold-checker image, then invoke this repository's `bin/cold-cards` on a warm-run directory containing `cards.tsv`, `cards/` and `out/`:

```sh
DOCKER_BUILDKIT=1 docker build -f docker/cold-checker/Dockerfile -t hol-hearth-cold-checker .
HEARTH_CHECKOUT=/path/to/hol-hearth /path/to/openai-math-hol-cards/bin/cold-cards WARMDIR OUTDIR
```

The revised cold wrapper requires successful worker execution and exact expected receipt membership before reporting PASS. The 2026-10-08 Pro review inspected the existing complete receipt set; it did not rerun every proof.

## License and attribution

Original code is available under the MIT License in [LICENSE-MIT](LICENSE-MIT). Original prose is available under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). See [LICENSE.md](LICENSE.md) for scope and attribution.

Excerpts and adaptations from `openai/math` retain their Apache-2.0 terms and attribution. The release license is preserved in `third_party/openai-math/LICENSE`. Original contributions do not relicense third-party material.
