# Publication check, 2026-10-08

Checked commit: `fc38bb4fb502299e792aa2d8bcbfded9da82ab52`, the reviewed revisions applied to `9d1776eb1b233a17ad6599bcdce7bd7268e1d170`.

## Card 196 with the revised plain runner

- Command: `HOLDIR=<hol-light> bin/replay-plain <out>/plain-196 196`, run once from a fresh clone.
- HOL Light `2a1cea8f1cb7f3885a60d947ba06eabac6ec1d32` (clean checkout, built by Hearth's setup), OCaml 5.4.0, Linux x86_64 on bluestar26.
- 2026-10-08 12:54:09Z to 13:06:26Z. Exit status 0.
- Result: `PLAIN 196 light PASS: 2/2 files behaved as expected`. The leaf `kaplansky196_bounds.ml` loaded cleanly and `K196_RATIONAL_BOUNDS` type-checked as `thm`. The control `negctl_kaplansky196_below_99_100.ml` raised `Failure "TAC_PROOF: Unsolved goals"` while its source loaded.

The evidence is in [`plain-196-20261008T125409Z/`](plain-196-20261008T125409Z/):

| File | Contents |
|---|---|
| `run.cmd`, `run.sh` | the command and the wrapper that recorded its status |
| `context.txt` | repository commit, HOL Light commit, OCaml version, host kernel |
| `run.time`, `run.exit`, `run.stdout`, `run.stderr` | timing, exit status and the runner's own output |
| `plain-196/summary.txt`, `plain.tsv`, `details.json` | the runner's verdicts |
| `plain-196/logs/*.log.in` | the exact input sent to each HOL process |
| `plain-196/logs/*.log` | the raw HOL output for each file |

This checks the revised runner against real HOL Light for one card and its control. It does not rerun the other cards. The summaries in `evidence/plain/` were produced by the earlier runner and remain records of those runs only.

## Runner fixtures

The review's fixture suites passed against the same commit: 11/11 for `bin/replay-plain` and 16/16 for `bin/cold-cards`. They use fake checker processes, with no HOL Light or Docker. The fixture scripts belong to the review and are not part of this repository.

## Evidence reconciliation

`cards.tsv` names 29 files: 15 positive leaves and 14 controls. `evidence/cold/` keeps all 30 cold attempts. The final record for each of the 29 files is successful. One earlier attempt, card 369 `hotspots369_bessel.ml`, ended when HOL was killed for memory. It is kept and not counted as a receipt.
