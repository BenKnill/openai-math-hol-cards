# Card 188: Random triangle removal: Spencer's law

**Publish gate:** `188`: warm **PASS**, cold **PENDING**. **Not cleared: do not advertise this card** until the gate passes.

| | |
|---|---|
| Family | 188, "The sharp terminal leave in random triangle removal." (release `CONTENTS.md`) |
| Release paper | `preprints/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026.pdf`, *The sharp terminal leave in random triangle removal* |
| Where | Spencer's heuristic: an edge's survival probability q solves dq/dt = −Dq³. |
| Profile | `heavy` |
| Leaves | `triangle188.ml` |
| Negative control | `negctl_triangle188_one_partner.ml` |
| Release Lean | `lean/docs/188.md`; comparator config `TriangleRemoval` |
| Release | github.com/openai/math at commit `adc7f124` (2026-10-06) |

## Exact statement

The kernel-checked conclusion of each headline binding, exactly as `hearth inspect --binding` printed the matched source statement (HOL Light syntax: `&n` is the real n, `!` is ∀, `/\` is ∧, `inv` is 1/x). Full inspect output: `evidence/`.

`TR188_SPENCER_CARD`:
```
(!D. &0 <= D ==> inv(sqrt(&1 + &2 * D * &0)) = &1 /\ !x. &0 <= x ==> ((\t. inv(sqrt(&1 + &2 * D * t))) has_real_derivative (--D * inv(sqrt(&1 + &2 * D * x)) pow 3)) (atreal x)) /\ ((\n. ((&n pow 2 / &2) * inv(sqrt(&1 + &2 * &n))) / (&n * sqrt(&n))) ---> inv(&2 * sqrt(&2))) sequentially
```

## What HOL certifies

- `TR188_SPENCER_LAW`: for every D ≥ 0, q(t) = (1 + 2Dt)^{−1/2} has q(0) = 1, and at every t ≥ 0 its real
  derivative (two-sided, `has_real_derivative … (atreal t)`) is −D·q(t)³.
- `TR188_LEAVE_CONSTANT`: (n²/2)·(1 + 2n)^{−1/2} / (n·√n) → 1/(2√2) as n → ∞ (the leaf writes n^{3/2} as n·√n).
- `TR188_SPENCER_CARD` is both statements in one theorem.

## What HOL does not certify

- Anything about the random process. That q is an edge's survival probability is Spencer's heuristic, which
  treats partner edges as independent; making that rigorous is the paper's whole job. Credit Spencer's heuristic.
- The theorem itself (terminal edges / n^{3/2} → 1/(2√2) in L²).
- Uniqueness of the ODE solution.

## Relation to the release's Lean coverage

"Lean" below means the release's selected statement, as described in its `lean/docs/NNN.md`; this repository does not rebuild or re-run that Lean.

The theorem (L² limit 1/(2√2)) is Lean-formalized in the release (`lean/docs/188.md`). This card checks only
the heuristic's arithmetic.

## Verdicts

Control from the heavy lane: the "one partner" law q′ = −D·q² for the same q, same tactic.

Warm: Hearth on bluestar26 (hol-hearth 02443c8, HOL Light 2a1cea8), run `bluestar26:~/lanes/math-hol-cards/work/20261007T195855Z-a2c3f78`, fresh replay of every file (`--force`).

| Card | Kind | File | Warm verdict (exact first line) | Cold verdict |
|---|---|---|---|---|
| 188 | leaf | `triangle188.ml` | `PASSED triangle188.ml: 7/7 bindings proved, 0 new axioms, eval 2.1s (heavy)` | pending |
| 188 | control | `negctl_triangle188_one_partner.ml` | `FAILED negctl_triangle188_one_partner.ml at NEGCTL_TR188_ONE_PARTNER_LAW (line 28): Exception: Failure "REAL_ARITH '~(q * inv q = &1) \\/\n(~(&0 < q) \\/ &0 = q) \\/\n--((&0 + &2 * D * &1) * inv (&2) …` | pending |

The original lane receipts (before this repository) are listed in the lane's `RESULTS.md` / `RECEIPTS.md` named under Sources.

## Sources

Math-drop lane, `~/lanes/math-drop-2026-10-07/` (Ben's machine): `b26-hol/triangle188.ml`, `b26-hol/RESULTS.md` §188; SLATE.md HOL table row 188. Copies and their sha256 are in `../../PROVENANCE.tsv`.
