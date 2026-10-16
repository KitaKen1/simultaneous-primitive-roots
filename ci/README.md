# Local checks and GitHub Actions

All Lake projects, including the small comparator controls, use Lean `v4.33.1`.
Mathlib and both checking tools are fixed in [toolchain-lock.json](toolchain-lock.json). The tools are vendored so a
moving upstream branch cannot change the check. The comparator/exporter code is
unchanged from the pinned upstream commits; only their toolchain and dependency
configuration are adjusted.

From the repository root:

```bash
python3 scripts/check_sources.py
# After refreshing the completed migration records:
python3 scripts/check_sources.py --check-port-record
bash scripts/build.sh
(cd tools/fc-style && lake build)
python3 scripts/check_fclike_standalone.py
bash scripts/compare.sh local-development   # macOS development only
```

The first command checks that the two submitted variants match their independent
Challenge declarations, dependencies are pinned, and proof source under `lean/` has no proof holes or extra
axioms outside the two intentional Challenge placeholders. Comments and strings
are excluded from the scan. This source scan supplements the compiler and
comparator; it is not a substitute for them.
The additional port-record check verifies every changed source digest, accounts
for the new backports, and reconstructs the original files from the recorded
patch to check their original digests. CI requires this check.

`build.sh` obtains the official Mathlib cache, builds Challenge and Solution, and checks
the axiom reports for both submitted proofs and the separate square-condition supplement.
`compare.sh` uses the upstream comparator to build and export
Challenge and `Solution` independently, compare the two submitted target types and their dependencies,
check the allowed axioms, and replay the solution in a fresh Lean kernel.
Challenge imports only Mathlib and contains exactly the two submitted statements,
with no problem-specific definitions. The conditional OpenAI reference and square
obstruction remain separate source files outside this Comparator configuration.

The upstream macOS development shim does not provide Linux sandboxing. For the
Linux command, set `COMPARATOR_LANDRUN` to the pinned Landrun binary and run:

```bash
bash scripts/compare.sh linux
```

The workflow compiles the independent statements separately. Cold proof compilation
is divided into foundation jobs, a downstream Hecke-boundary job, and final proof
assembly. Each component uses the unchanged `Comparator.safeLakeBuild` and real
Landrun. Build files are shared only within the same workflow run and commit;
[component targets](component-targets.json) define deterministic ownership of
shared modules. Archives include companion artifacts and per-file SHA256 hashes.
The restore step verifies commit, source, toolchain and configuration identities,
module coverage and safe paths before restoring anything.

The final job rebuilds the canonical Challenge from source, then runs the unchanged
two-target Comparator, dependent-definition comparison, axiom audit and fresh
kernel replay. Compilation artifacts cannot replace those checks. Only the
checking tools' build directories are cached across workflow runs; Mathlib comes
from its official pinned cache.

Every proof runner removes unused SDKs only on a disposable GitHub-hosted runner,
provisions 8–16 GiB of swap while reserving 36 GiB of build disk, and tests a
20 GiB preflight before restoring proof components. The guarded build or comparison
records disk and memory every 30 seconds and aborts below 4 GiB free to preserve
logs. A separate control exercises an actual systemd-unit stop. Compressed Mathlib
download archives are pruned only after successful extraction.

Builds and full comparison run as an unprivileged user in a transient systemd unit
with AF_UNIX restricted. A native Lake launcher outside the candidate's writable
directory limits sandboxed builds to two workers. The pinned Comparator source
and all checking algorithms remain unchanged. Diagnostic logs are retained for
30 days; temporary same-run compilation archives are retained for one day.

## Intended rollout

1. Review the FC-style statement, unchanged PDF and root README locally.
2. Push the reviewed tree to the private `KitaKen1/ci-test-sandbox` repository and
   run `.github/workflows/lean.yml` there.
3. After the private run passes and its commit is reviewed, put the same source
   tree in `KitaKen1/simultaneous-primitive-roots` and run the same workflow.
4. Link the public run for the tested commit when documenting CI success.

Private testing is on `ci/simultaneous-primitive-roots-lean4331` in [ci-test-sandbox](https://github.com/KitaKen1/ci-test-sandbox/actions/workflows/lean.yml). The current configuration is recorded in [two-variant-review.json](two-variant-review.json). Public results are listed in [the public workflow](https://github.com/KitaKen1/simultaneous-primitive-roots/actions/workflows/lean.yml).
The existing v4.35.0-rc3 evidence is historical evidence for the original
workspace, not evidence that the v4.33.1 publication build or CI passed.

See [STATUS.md](STATUS.md) for current local results.

The FC statements use the actual `FormalConjecturesUtil` import and
`category research solved, AMS 11` attributes. Their separate project in
`tools/fc-style/` pins the official FC revision and the same Mathlib/Lean 4.33.1.
The proof and Comparator projects continue to use the independent Mathlib-only Challenge.
The FC files include `[OAI26]` / `[Ki26]` references and `formal_proof using lean4 at "…"` attributes. Their URLs name the fixed proof-snapshot commit; the links become available when the prepared candidate is published.
