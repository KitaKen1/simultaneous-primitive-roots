# Verification status

Current submission: the two variants in `FClikelean/SimultaneousPrimitiveRoots.lean`.
Lean and Mathlib are pinned to 4.33.1.

| Check | Current status |
|---|---|
| Independent Challenge | Mathlib only; two statements, no problem-specific definitions |
| FC statement correspondence | Both Challenge types exactly match the submitted FC file |
| Comparator | Challenge against Solution; only the unconditional prime-base theorem and stronger variant |
| Source and migration audit | Passed; proof bodies unchanged, two intentional Challenge placeholders |
| Local Challenge and Solution build | Passed; submitted proofs use only `propext`, `Classical.choice`, `Quot.sound` |
| FC-style build | Passed; submission, conditional reference and supplement compile separately |
| Private Linux CI | [Passed](https://github.com/KitaKen1/ci-test-sandbox/actions/runs/38860344650) at 22:01 JST on 16 October 2026; both submitted targets, comparator controls, axiom checks and kernel replay succeeded |
| Public Linux CI | [Public Actions](https://github.com/KitaKen1/simultaneous-primitive-roots/actions/workflows/lean.yml); the same two-target configuration is being submitted for a fresh run; no public success claimed yet |

The current configuration and hashes are in [two-variant-review.json](two-variant-review.json).
The OpenAI conditional reference and square-condition supplement remain separate
from the FC submission and are not Comparator targets.

The previous four-target private run and the older two- and three-target checks
are historical. They do not establish success of this new run. Their records
remain in [four-target-review.json](four-target-review.json),
[three-theorem-review.json](three-theorem-review.json), and
[local-verification.json](local-verification.json).
