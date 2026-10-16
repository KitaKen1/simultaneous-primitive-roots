# Verification status

Snapshot prepared on 16 October 2026 (Asia/Tokyo), stock Lean 4.33.1.

| Check | Status at snapshot time |
|---|---|
| FC submission file | Unconditional prime-base corollary and stronger integer-base variant only; no problem-specific definitions |
| Conditional reference | Four-input statement and five definitions in the separate `FClikelean/OpenAIConditional.lean`; outside the proposed FC submission; paper correspondence remains under review |
| Independent Challenge | All four input hypotheses and their density definition, main, both variants and the supplement; imports only Mathlib |
| Comparator targets | All four theorems, including conditional main and its dependent definitions |
| Challenge ↔ FC files ↔ proof | All four statement types still match. The conditional statement and its five definitions now match the separate reference file. |
| Proof builds and four public axiom reports | Passed; exactly `propext`, `Classical.choice`, `Quot.sound` |
| FC format and standalone statements | Three files built using real FC utilities on Lean 4.33.1; separate standalone checks and the layout receipt are recorded in `fc-submission-layout.json` |
| Source and migration audit | Passed; 4,465 proof files, 1,251 ported sources, 22 backports and the main bridge accounted for |
| Private Linux CI | [Statements and all five foundation builds passed](https://github.com/KitaKen1/ci-test-sandbox/actions/runs/38818388877). Attempt 2 resumed the failed jobs on 16 October at 04:42 UTC, reusing the successful foundation builds. Hecke assembly is in progress; full comparison and replay remain pending. |
| Public Linux CI | Candidate prepared locally; publication requires explicit approval |

The four current targets are:

- `SimultaneousPrimitiveRootsChallenge.simultaneous_primitive_roots`
- `SimultaneousPrimitiveRootsChallenge.simultaneous_primitive_roots_unconditional`
- `SimultaneousPrimitiveRootsChallenge.positive_lower_density`
- `SimultaneousPrimitiveRootsChallenge.square_condition_necessary`

[Challenge.lean](../lean/Challenge.lean) is independent of the proof library.
[OpenAIMain.lean](../lean/SimultaneousPrimitiveRootsFinal/OpenAIMain.lean)
imports `Solution` and proves the exact conditional main from the unconditional
corollary. The other three proofs are in [Solution.lean](../lean/Solution.lean).
This does not prove the four hypotheses themselves.

The FC submission is limited to `simultaneous_primitive_roots_unconditional`
and `positive_lower_density`. The conditional reference and square obstruction
remain separate supplementary files. This layout change does not alter any proof
source, Challenge, or the four-target Comparator configuration. The in-progress
private run checks the preceding publication snapshot; local checks separately
validate the new file layout. See [fc-submission-layout.json](fc-submission-layout.json).

The current configuration and source hashes are in
[four-target-review.json](four-target-review.json).
Historical two-target and three-target checks are preserved in
[local-verification.json](local-verification.json) and
[three-theorem-review.json](three-theorem-review.json). Neither is a four-target CI result.
The three-target macOS run captured its exports before this update and passed
kernel replay; its completion receipt is `results/three-theorem-comparator-run.json`.

The private CI workflow provisions swap on its ephemeral Linux runner and uses
real Landrun. The FC files are built in the separate pinned `tools/fc-style/`
project. Their proof URLs name the fixed proof-snapshot commit; the links become
available when the prepared candidate is published.

Attempt 1 stopped before executing any Hecke-job step because GitHub did not
permit the job to start. Attempt 2 is now running after the account restriction
was lifted. Local diagnostic details and successful component archives are
retained under the ignored `ci/results/` directory. Complete four-target
comparison and fresh kernel replay still need to finish.
