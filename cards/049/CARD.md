# Card 049: A stable coordinate: the explicit change of variables

**Publish gate:** `049`: warm **PASS**, cold **PASS**. Cleared: every leaf reproduced cold and every control failed cold at its warm binding.

| | |
|---|---|
| Family | 049, "A stable-coordinate counterexample in four variables." (release `CONTENTS.md`) |
| Release paper | `preprints/A-stable-coordinate-that-is-not-a-coordinate-in-four-variables-October-5-2026/stable-coordinate-four-variables.pdf`, *A stable coordinate that is not a coordinate in four variables* |
| Where | `build/source/sections/02-construction.tex`, Props 2.1–2.2. The lead checked that f and Q match the paper's Thm 1.1. |
| Profile | `light` |
| Leaves | `stable_coordinate_049.ml`, `stable_coordinate_049_assembled.ml` |
| Negative control | `negctl_stable_coordinate_049_wrong_f.ml` |
| Release Lean | `lean/docs/049.md` (a different paper of the family) and `lean/docs/047.md` |
| Release | github.com/openai/math at commit `adc7f124` (2026-10-06) |

## Exact statement

The kernel-checked conclusion of each headline binding, exactly as `hearth inspect --binding` printed the matched source statement (HOL Light syntax: `&n` is the real n, `!` is ∀, `/\` is ∧, `inv` is 1/x). Full inspect output: `evidence/`.

`SC049_STABLE_COORDINATE`:
```
(!z. SC_PSI(SC_PHI z) = z) /\ (!y. SC_PHI(SC_PSI y) = y) /\ (!p s u n v. SC_F(SC_PHI(p,s,u,n,v)) = p)
```

## What HOL certifies

`SC049_STABLE_COORDINATE`: two explicit polynomial maps on ℝ⁵ are mutually inverse and send the paper's
f = x₁ − 2Q(Q(x₂+x₄) + x₁x₄), with Q = x₂² − x₄² + x₁x₃, to the first coordinate.

Here `SC_PHI = ι∘exp(wΔ)∘π` and `SC_PSI = π⁻¹∘exp(−wΔ)∘ι⁻¹` are the point maps of the paper's three ring
isomorphisms, written out as explicit polynomials. The only division is by 2. The proof uses 26 lemmas (the
flow fixes `x` and sends `H` to `H+pw`; the matrix shear `(I ∓ 2neᵗ)`; the unimodular `(F,J) ↔ (L,N)` change;
`H = L − u + pQ0`). `stable_coordinate_049.ml` is the scout's first, smaller leaf (8 bindings: the flow and
the linear coordinates); `stable_coordinate_049_assembled.ml` (30 bindings) is the full statement.

## What HOL does not certify

- The standard step from "mutually inverse polynomial maps with rational coefficients on ℝ⁵" to a ℚ-algebra,
  hence ℂ-algebra, automorphism of ℂ[x₁..x₄, w]. This is one line of algebra but is not formalized.
- The hard half: that f is **not** a coordinate of ℂ[x₁..x₄]. That is the derivation and filtration
  obstruction in §§3–5; the paper claims it, and it is paper-only.

## Relation to the release's Lean coverage

"Lean" below means the release's selected statement, as described in its `lean/docs/NNN.md`; this repository does not rebuild or re-run that Lean.

`lean/docs/049.md` covers only the family's **September 24** paper, a **different** polynomial F
(ℂ[x]/(F) ≅ ℂ^[n−1], F not a coordinate, n ≥ 4). `lean/docs/047.md` says: "The separate stable-coordinate ...
consequences are not included." So the October 5 theorem is paper-only in the release, and this card checks
its construction half (the slate: "this theorem was paper-only").

## Verdicts

Control from the scout: f written with x₂ − x₄ in place of x₂ + x₄. It fails at `SCA_F_IOTA`.

Warm: Hearth on bluestar26 (hol-hearth 02443c8, HOL Light 2a1cea8), run `bluestar26:~/lanes/math-hol-cards/work/20261007T195855Z-a2c3f78`, fresh replay of every file (`--force`).

| Card | Kind | File | Warm verdict (exact first line) | Cold verdict |
|---|---|---|---|---|
| 049 | leaf | `stable_coordinate_049.ml` | `PASSED stable_coordinate_049.ml: 8/8 bindings proved, 0 new axioms, eval 2.7s (light)` | reproduced (189s) |
| 049 | leaf | `stable_coordinate_049_assembled.ml` | `PASSED stable_coordinate_049_assembled.ml: 30/30 bindings proved, 0 new axioms, eval 3.8s (light)` | reproduced (196s) |
| 049 | control | `negctl_stable_coordinate_049_wrong_f.ml` | `FAILED negctl_stable_coordinate_049_wrong_f.ml at SCA_F_IOTA (line 269): Exception: Failure "find".` | failed at the warm binding, as designed (286s) |

Cold: Hearth's cold checker (`dev/cold-check`, hol-hearth 32862cd, which is 02443c8 plus one unrelated commit (68d79ad, Btrfs device support), run on the OrbStack Linux machine dev, image `hol-hearth-cold-checker:cards-32862cd`): HOL Light 2a1cea8 built from pinned sources in Docker with `--network none`, no Hearth runtime, CRIU or warm state. Leaves must reproduce; controls run with `--expect-failed` and must fail cold at the binding that failed warm. Run `dev:~/lanes-runs/math-hol-cards/cold/20261007T200529Z-a2c3f78 (heavy, three at a time), -light (light, one at a time) and -phase2 (the 150 receipts, the 369 retry and one 369 control, two at a time)`.

The original lane receipts (before this repository) are listed in the lane's `RESULTS.md` / `RECEIPTS.md` named under Sources.

## Sources

Math-drop lane, `~/lanes/math-drop-2026-10-07/` (Ben's machine): `hol-pilots/` (`RECEIPTS.md`, both leaves, the control); `scouts/hol-fast-follows.md` §1; SLATE.md HOL table row 049. Copies and their sha256 are in `../../PROVENANCE.tsv`.
