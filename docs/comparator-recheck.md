# Comparator definition holes: configuration and re-check results

2026-10-08 · Release examined: [`openai/math` at `adc7f124`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a)

We independently re-ran a subset of the release’s Lean checks, using its pinned Lean 4.34.1 and Mathlib, with comparator v4.34.0 rebuilt for that Lean version. We found no substantive definition change in the cases inspected. These results also illustrate a documented boundary of the release’s check configurations.

## What a definition hole permits

A name in `definition_names` is a definition hole. Comparator checks its name, type, universe parameters and safety; its body need not match the challenge. Comparator’s [implementation](https://github.com/leanprover/comparator/blob/d03acab154d269c06e60e4de7e4cc85deebff94b/Comparator/Compare.lean) and [README](https://github.com/leanprover/comparator/blob/d03acab154d269c06e60e4de7e4cc85deebff94b/README.md#definition-holes) document this behavior and the requirement for an additional verifier.

Nine of the release’s 405 configurations use holes. In seven, every listed hole is a definition written out in the challenge. Some carry the statement’s content: [OccupiedOverlap](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/OccupiedOverlap.lean) states its two theorems as `OccupiedOverlapEndpoint`, a hole of type `Prop`; SpinAngle uses the holes `phi`, `row` and `column`; KServer’s theorem has type `MainStatement`, also a hole. A changed body can therefore pass the configured comparison if the remaining checks succeed.

## Observed results

For 17 release configurations, we ran Hearth-generated strict checks with no definition holes and challenge theorem declarations as targets:

- **15 passed**, using only the permitted standard axioms: `propext`, `Quot.sound` and `Classical.choice`. Five were configurations with fully written holes: EuclideanFiveColor (158; one hole), Brenier (12), KServer (9), Naimark (7) and Rokhlin (4). Their 33 listed hole bodies matched. A separate control changing the 158 challenge to `Fin 6` was rejected.
- **OccupiedOverlap and SpinAngle were refused by strict comparison**, but passed their original release configurations. Supplementary diagnostics explain the observed strict mismatches below.

In SpinAngle, `missingInRow` and `occupiedRow` agree after consistently renaming their universe parameters by position. The three holes themselves agree under the same structural equality used by comparator.

In OccupiedOverlap, `OccupiedOverlapEndpoint` differs in a proof argument for `Nat.AtLeastTwo (1 + 1)`, used in the instance for the literal `2`. The auxiliary proofs have the same proposition type. The expression dumps otherwise match after substituting that proof name, consistent with Lean’s definitional proof irrelevance. The other four holes match structurally.

The diagnostic recorded kernel acceptance of the corresponding `Eq.refl` comparisons in the solution environment. The combined tally for the seven configurations is **40 structural matches and one reported kernel-definitional match across 41 hole declarations**. That declaration tally does not by itself establish complete dependency equivalence.

ElementaryPositivity, an eighteenth release configuration, passed its original configuration. Its challenge intentionally leaves the witness body as `sorry`. Its witness type carries the required expansion property; reviewing whether that type expresses the intended informal theorem remains a separate task.

We did not run DefocusingNLS. Its hole `sobolevProduct` includes a `sorry` membership proof inside an otherwise written definition; `schrodingerFlow` and `sobolevOddPower` are written out. The configured hole comparison leaves all three bodies, including `sobolevProduct`’s data component, uncompared.

## Suggested follow-up and scope

Consider reserving holes for intentionally omitted bodies, or documenting the additional verifier for fully written definitions. Removing these holes already passes in the five configurations above. OccupiedOverlap and SpinAngle additionally need their syntactic differences addressed or a validated comparison preserving the full relevant dependency context. Developing that comparison is future work; equality after interpreting both expressions in the solution environment is insufficient by itself.

The supplementary diagnostics use imported elaborated environments, a restricted traversal, and selected auxiliary-name exclusions. They are not a replacement for comparator’s export and replay checks. The results cover this tested subset and do not establish that every formal statement captures its informal problem. The work used AI assistance.
