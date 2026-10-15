# Verification status

Snapshot prepared on 16 October 2026 (Asia/Tokyo), stock Lean 4.33.1.

| Check | Status at snapshot time |
|---|---|
| FC central file | Conditional main, unconditional prime-base corollary, stronger variant, in that order |
| Independent Challenge | All four input hypotheses and their density definition, main, both variants and the supplement; imports only Mathlib |
| Comparator targets | All four theorems, including conditional main and its dependent definitions |
| Challenge ↔ FC ↔ proof | Main and all five definitions match; the four Challenge statements match the FC statements |
| Proof builds and four public axiom reports | Passed; exactly `propext`, `Classical.choice`, `Quot.sound` |
| FC format and standalone statements | Passed using real FC utilities on Lean 4.33.1; reference keys and proof URLs included |
| Source and migration audit | Passed; 4,465 proof files, 1,251 ported sources, 22 backports and the main bridge accounted for |
| Private Linux CI | [Staged compilation running](https://github.com/KitaKen1/ci-test-sandbox/actions/runs/38818388877); previous full job hit the six-hour compilation limit |
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
