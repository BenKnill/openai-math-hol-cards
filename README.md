# openai-math HOL Light cards

Small HOL Light certificates ("cards") for steps of twelve results in the OpenAI math release
([github.com/openai/math](https://github.com/openai/math), commit `adc7f124`, 2026-10-06), each with a negative
control, a statement of exactly what HOL certifies and what it does not, and how the card relates to the release's
own Lean coverage. They were made as on-screen "what is certified, and what is not" cards for short math films.

**Private draft for Ben's review. Nothing here is published.** License: **TBD by Ben** (see the end).

**Status (2026-10-07 21:21 UTC):** 12/12 cards PASS warm (every leaf PASSED, every control FAILED as designed;
fresh replays on bluestar26); the cold gate is still running. A card that fails cold is marked in its `CARD.md` and must not be
advertised.

None of these cards proves a headline theorem of the release. Each checks one step, one number, or one piece of
algebra, and each `CARD.md` says what is left out. Read a card before quoting it.

## Summary

| Card | Family | What HOL certifies | Beyond the release's Lean | Profile | Warm | Cold |
|---|---|---|---|---|---|---|
| [158](cards/158/CARD.md) | 158 · The Euclidean plane cannot be colored with five colors | The seven placed Moser vertices lie in the three-label region, the 11 edges have length exactly 1, and no proper 3-labelling exists; exact arithmetic in ℚ(√3,√11) | Independent method for a Lean-covered step | `light` | PASS (26/26) | pending |
| [049](cards/049/CARD.md) | 049 · A stable-coordinate counterexample in four variables | Two explicit polynomial maps on ℝ⁵ are mutually inverse and send the paper's f to the first coordinate | Checks the construction half of a result that is paper-only in the release; the hard half (f is not a coordinate in 4 variables) stays paper-only | `light` | PASS (8/8; 30/30) | pending |
| [353](cards/353/CARD.md) | 353 · Affine Bernstein rigidity through dimension nine and a smooth dimension-ten counterexample | The algebra of the invariant box: stationary corner (9/2, 7/2, 33/7), face signs, the D-equation from the C-equation | Checks algebra inside a result that is paper-only in the release (Lean covers dimensions 3–9 only); the ODE and PDE reduction are not covered | `light` | PASS (4/4) | pending |
| [354-light](cards/354/CARD.md) | 354 · The isoperimetric profile of the cubic three-torus | Switch volumes 4·PI/81 and 1/PI and the radii there, for any positive constant PI | Cross-check of a Lean-covered result; on-screen value | `light` | PASS (4/4) | pending |
| [354-pi](cards/354/CARD.md) | 354 · The isoperimetric profile of the cubic three-torus | The same with HOL's real π: ties at 4π/81 (radii 1/3, 2/9) and at 1/π (area 2); the ball loses at 1/π | Cross-check; minimality is Lean's | `heavy` | PASS (10/10) | pending |
| [196](cards/196/CARD.md) | 196 · A counterexample to Kaplansky’s zero-divisor conjecture | The paper's two exact rationals and both bounds < 149/150 | Cross-check of a Lean-covered result; on-screen value | `light` | PASS (1/1) | pending |
| [028](cards/028/CARD.md) | 028 · Uniformly bounded components of Gaussian-prime graphs | A finite nonempty set in the plane is not invariant under a nonzero translation | Cross-check of a Lean-covered result; on-screen value | `light` | PASS (1/1) | pending |
| [325](cards/325/CARD.md) | 325 · The complete Crouzeix conjecture | x² + y² = 1 ⇒ \|2xy\| ≤ 1 (real form of the sharpness case) | Cross-check of a Lean-covered result; on-screen value | `light` | PASS (1/1) | pending |
| [017](cards/017/CARD.md) | 017 · The irrationality exponent of π is 2 | 2.664·10⁻⁷ < 355/113 − π < 2.669·10⁻⁷ and 24.5 < 1/(355³ sin² 355) < 24.7, so the Flint–Hills partial sum through n = 355 exceeds 24 | Hook card; Flint–Hills convergence stays paper-only | `heavy` | PASS (8/8) | pending |
| [188](cards/188/CARD.md) | 188 · The sharp terminal leave in random triangle removal | q = (1+2Dt)^(−1/2) solves q′ = −Dq³ with q(0) = 1, and the leave constant tends to 1/(2√2) | The heuristic's arithmetic only; nothing about the random process | `heavy` | PASS (7/7) | pending |
| [369](cards/369/CARD.md) | 369 · The hot spots conjecture for simply connected planar domains | The J₁ power series has derivative J₀ − J₁/x on (1, 2), and it vanishes somewhere in (1.8411, 1.8412) | Illustration; not that this is the first zero, nor that the series are "the" Bessel functions | `heavy` | PASS (16/16; 24/24; 27/27) | pending |
| [150](cards/150/CARD.md) | 150 · Weak mixing of triangular billiards with an irrational angle | Counting step only: at most ⌈π/α⌉ multiples of α fit in an open interval of length π | Not the bounce claim; the unfolding geometry is not certified | `heavy` | PASS (5/5) | pending |

Warm = Hearth (`hearth prove --force`) on bluestar26: hol-hearth 02443c8, HOL Light 2a1cea8; bindings proved per leaf in
parentheses. Cold = Hearth's cold checker (`dev/cold-check`): HOL Light rebuilt from pinned sources in Docker with no
network and no Hearth runtime; leaves must reproduce and controls must fail at the same binding as warm.
Raw verdicts: `evidence/warm/`, `evidence/cold/`.

Cards 196, 028, 325 and 354-light were one batch file in the lane (`onscreen_light_batch.ml`); here each family's
block is split out verbatim into its own leaf. Those four cards, and 353, had no negative control in the lane: the
controls in their directories were written for this repository (each reuses the leaf's tactic on a false variant).
Everything else is copied byte for byte from the lane; `PROVENANCE.tsv` lists every copied file with its sha256.

## Honesty rules for this drop (from all scouts)

1. **"Lean" means a selected statement.** Read `lean/docs/NNN.md` for each claim. 49 docs name
   parts of their papers that fall outside the formalization. The catalogue's own metadata says
   `review: unchecked`.
2. **Folder dates are not discovery dates.** Lean coverage is 57% for papers dated Sept 22–27
   and 3% for Sept 30–Oct 6 (the lead spot-checked these numbers).
3. **Paper-only results get "the paper claims"**, per the README's "could have issues".
4. **The reasoning traces are mostly a summarizer's narration.** Only the boxed excerpts are verbatim.
5. **Provenance:** 213 cites earlier AI and Lean work, 325 (Crouzeix) has other 2026 proofs,
   366 (Mumford–Shah) has a parallel proof, and 165's papers cite a 2018 claim. Never say "first".
6. **We have not compiled any Lean.** Every "no `sorry`" above is a grep result. `lean-158/`
   is the first real re-run; its result is reported there.
7. **The release's comparator configs sometimes leave definitions unchecked.** The Lean agent found
   this and the lead verified it in comparator's source and README. Any name listed under
   `definition_names` is a "definition hole": comparator checks only its name, type, universes
   and safety, not its body. The README says such holes "can be gamed" and need an additional
   verifier. **9 of 405** release configs use holes.
   - In **7** of them, every hole is a definition the challenge writes out in full: Brenier,
     EuclideanFiveColor (158), KServer, Naimark, OccupiedOverlap, Rokhlin and SpinAngle. As
     configured, the release's check would accept a solution that silently redefined those terms.
   - **ElementaryPositivity** and **DefocusingNLS** have genuine `sorry` holes, which is the
     intended use. DefocusingNLS mixes them with complete definitions.
   - For 158 the lead read both definitions. The solution's `ProperColoring` matches the
     challenge's up to variable names, so the result stands. The bluestar26 re-check (rule 8) has since
     confirmed this by machine.
   - The other 8 need the same by-hand comparison before their Lean status is quoted in a film.
8. **The Lean re-check of 158 PASSED on bluestar26 (2026-10-07, about 15:00).**
   - **Result:** `1/1 theorems matched`, with only the standard axioms (Lean 4.34.1, Mathlib d13f23b, comparator 46f1cef, landrun sandbox). Wall time was 1059 s.
   - **The definition hole is closed by machine.** This run did not pass `definition_names`, so comparator required `ProperColoring`'s body to be identical, and it was.
   - **Negative control:** the Fin-6 version was REFUSED, as it should be.
   - **Sibling:** the 7-coloring theorem also passed.
   - **Why bluestar26:** on `dev` the check had stalled on page cache.
   - **Hearth revision:** the shared hearth 02443c8 had moved its Lean lane to a separate repo, so the lane ran from a clean clone at cd1a660, the revision dev used.
   - **Remaining families:** still running; see `b26-lean/RESULTS.md`. It is now fair to say in the 158 film that "we re-ran the Lean check".

*Copied verbatim from the lane's `SLATE.md` (sha256 `b7d9d4b15b9308af…`, read 2026-10-07 21:21 UTC). Paths in the rules
(`lean-158/`, `b26-lean/`, `lean/docs/`) refer to the lane directory and to the release. For these cards: "the paper
claims" applies to every paper-only statement a card mentions, and none of the cards may be described as a "first".*

## Reproduce

All leaves are plain HOL Light source. HOL Light commit `2a1cea8f1cb7f3885a60d947ba06eabac6ec1d32`. Two profiles:

| Profile | Recipe (`replay/<profile>.ml`, byte-identical to Hearth's `profiles/<profile>.ml`) | Cards |
|---|---|---|
| `light` | `calc_rat.ml`, `prioritize_real()`, `Library/ringtheory.ml`, `RING_TAC` bound to `CONV_TAC REAL_RING`; sha256 `52a80fa1…6fb6` | 158, 049, 353, 354-light, 196, 028, 325 |
| `heavy` | `calc_rat.ml`, `prioritize_real()`, `Library/ringtheory.ml`, `Multivariate/realanalysis.ml`; sha256 `d7eaa073…5aed` | 354-pi, 017, 188, 369, 150 |

### With Hearth (warm; how the verdicts above were produced)

Hearth ([BenKnill/hol-hearth](https://github.com/BenKnill/hol-hearth), currently **private**) runs each file in a
fresh child of a warm HOL Light profile and records a receipt. On a Linux machine with a Hearth runtime that has
both profiles:

```sh
hearth doctor --profile light
hearth doctor --profile heavy

# one file
hearth prove cards/196/kaplansky196_bounds.ml --profile light --run-root out/runs-196 --force
hearth prove cards/017/pi355_017.ml           --profile heavy --run-root out/runs-017 --force
hearth inspect out/runs-017 --binding PI355_CERTIFICATE

# every card and control, one verdict line per card (needs a new OUTDIR each time)
HEARTH_BIN=hearth bin/run-cards out/warm-1           # or: make check-local
```

Ben's setup (bluestar26, warm): `make check` copies the cards to `~/lanes/math-hol-cards/work/<stamp>-<rev>/` on
bluestar26 over `ALLOW_METERED=1 ~/Documents/QUUD1GR-tailscale/bin/b26-ssh`, runs `bin/run-cards` there under
`~/lanes/bin/lane-run` (waiting with `lane-wait UNIT 480`), with
`HOL_WORKBENCH_RUNTIME_CONFIG=~/hearth/runtime.toml ~/src/hol-hearth/hearth`, and prints one line per card:

```
CARD 017       heavy PASS  PI355_CERTIFICATE: pi355_017.ml 8/8; control negctl_pi355_017_gt25.ml FAILED at NEGCTL_FLINT_HILLS_355_TERM_GT_25 (as designed)
```

`make check CARDS="158 017"` runs a subset. `bin/check-remote` documents `REMOTE_SSH`, `REMOTE_HEARTH` and friends
for other hosts. `run-cards` passes `--force` so every file is replayed fresh (Hearth otherwise reuses an earlier
receipt for byte-identical input and reports `UNCHANGED`); set `HEARTH_REUSE=1` to allow reuse.

### Cold (the publish gate)

In a hol-hearth checkout on Linux with Docker (BuildKit), build the cold-checker image, then replay every receipt
of a finished warm run (`WARMDIR` is the directory `run-cards` worked in: `cards.tsv`, `cards/`, `out/`):

```sh
DOCKER_BUILDKIT=1 docker build -f docker/cold-checker/Dockerfile -t hol-hearth-cold-checker .
HEARTH_CHECKOUT=~/src/hol-hearth bin/cold-cards WARMDIR out/cold-1
```

What was run here: the bluestar26 warm run `bluestar26:~/lanes/math-hol-cards/work/20261007T195855Z-a2c3f78` was copied to the OrbStack Linux machine
`dev` and checked with `HEARTH_CHECKOUT=~/src/hol-hearth-rc COLD_IMAGE=hol-hearth-cold-checker:cards-32862cd COLD_DOCKER='mac docker' COLD_STREAM=1 COLD_JOBS=3 bin/cold-cards WARMDIR OUTDIR`. A `light` receipt takes about 3 minutes cold and a `heavy` one
about 25 minutes (Multivariate is loaded from scratch).

### Plain HOL Light (no Hearth)

```sh
git clone https://github.com/jrh13/hol-light && cd hol-light
git checkout 2a1cea8f1cb7f3885a60d947ba06eabac6ec1d32 && make      # OCaml 5.3.0 and camlp5 8.03.01 were used cold
cd /path/to/openai-math-hol-cards
HOLDIR=/path/to/hol-light bin/replay-plain out/plain-1 196 017       # every card if no names are given
```

By hand, in `hol.sh` (use `replay/heavy.ml` for heavy cards):

```
loadt "/path/to/openai-math-hol-cards/replay/light.ml";;
loadt "/path/to/openai-math-hol-cards/cards/196/kaplansky196_bounds.ml";;
K196_RATIONAL_BOUNDS;;
```

`replay-plain` is weaker than Hearth: it checks that a leaf loads without an exception and that its bindings are
theorems, and that a control raises; it does not match statements or record receipts. 

## Layout

```
cards.tsv                 card, directory, profile, leaves, controls, headline binding
cards/NNN/CARD.md         the card: statement, certifies, does not certify, Lean relation, verdicts
cards/NNN/*.ml            proof leaves; negctl_*.ml are the negative controls
cards/NNN/evidence/       hearth inspect --binding output for each headline binding (warm run)
cards/158/gen/            regenerates the 158 leaf from exact normal forms (sympy)
bin/run-cards             warm check on this machine        bin/check-remote   warm check on a remote host
bin/cold-cards            cold publish gate (Docker)        bin/replay-plain   plain HOL Light replay
replay/light.ml, heavy.ml profile recipes                    evidence/          warm and cold verdict tables
PROVENANCE.tsv            every copied file, its source path in the lane and its sha256
third_party/openai-math/LICENSE   the release's license, verbatim
```

## License

**TBD by Ben.** This repository has no license file of its own yet; Ben will choose one before anything is published.

The release itself is under the Apache License, Version 2.0 (`/LICENSE` and `lean/LICENSE` in github.com/openai/math;
a verbatim copy is in `third_party/openai-math/LICENSE`). The cards reproduce short excerpts of the release: paper
titles and file paths, statements from the papers restated in HOL Light, and, in card 158, the two Lean definitions
of `ProperColoring`. The release's terms for redistribution:

```
   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and
```
