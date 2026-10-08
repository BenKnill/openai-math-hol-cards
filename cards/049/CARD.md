# Card 049: A stable coordinate: the explicit change of variables

**Publish gate:** `049`: warm **PASS**, cold **PASS**. Cleared: every leaf reproduced cold and every control failed cold at its warm binding.

| | |
|---|---|
| Family | 049, "A stable-coordinate counterexample in four variables." (release `CONTENTS.md`) |
| Release paper | **October 5, 2026:** [*A stable coordinate that is not a coordinate in four variables*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-stable-coordinate-that-is-not-a-coordinate-in-four-variables-October-5-2026/stable-coordinate-four-variables.pdf) |
| Where | `build/source/sections/02-construction.tex`, Props 2.1–2.2. The lead checked that f and Q match the paper's Thm 1.1. |
| Profile | `light` |
| Leaves | `stable_coordinate_049.ml`, `stable_coordinate_049_assembled.ml` |
| Negative control | `negctl_stable_coordinate_049_wrong_f.ml` |
| Release Lean | [Family 049 scope](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/049.md) covers the September 24 companion; [family 047 scope](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/047.md) excludes the separate stable-coordinate consequences. |
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
- The October 5 paper's claim that **this particular f is not a coordinate** of ℂ[x₁..x₄]. This card does not
  formalize its derivation and filtration obstruction in §§3–5. The selected Lean scopes cited below do not
  cover that stable-coordinate result; this does not imply that all noncoordinate results in family 049 are
  unformalized.

## Relation to the release's Lean coverage

"Lean" below means the release's selected statement, as described in its `lean/docs/NNN.md`; this repository does not rebuild or re-run that Lean.

The release **does have Lean coverage for family 049**. Its [scope document](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/049.md) links the
**September 24** paper, *An explicit noncoordinate polynomial with affine three-space zero fibre*.
The selected [Abhyankar–Sathaye statement](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/AbhyankarSathaye.lean)
says that for every n ≥ 4 there exists a noncoordinate polynomial F whose quotient is an affine-space
polynomial ring. The scope document also lists a companion result about commuting locally nilpotent
derivations. Do not describe those selected results, or the entire family, as paper-only.

This HOL card concerns the **October 5** stable-coordinate paper and its displayed polynomial f, not the
September 24 companion's F. The selected statements above do not state the explicit inverse maps checked
here. The release's [family 047 scope](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/047.md) also explicitly excludes the separate
stable-coordinate consequences. Thus any "beyond the release's Lean" label for this card refers specifically
to the October 5 construction. HOL certifies the displayed polynomial identities on ℝ⁵; it does not establish
the paper's complete stable-coordinate counterexample or the noncoordinate obstruction for this f.

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
