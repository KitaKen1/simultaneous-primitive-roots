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

The first command checks that the reviewed variants and supplement match their Challenge declarations, dependencies are pinned, and proof source under `lean/` has no proof holes or extra
axioms outside the four intentional Challenge placeholders. Comments and strings
are excluded from the scan. This source scan supplements the compiler and
comparator; it is not a substitute for them.
The additional port-record check verifies every changed source digest, accounts
for the new backports, and reconstructs the original files from the recorded
patch to check their original digests. CI requires this check.

`build.sh` obtains the official Mathlib cache, builds Challenge, Solution and the conditional-main bridge, and checks the
axiom reports for all four public proofs. `compare.sh` uses the upstream comparator to build and export
Challenge and `SimultaneousPrimitiveRootsFinal.OpenAIMain` independently, compare the four selected target types and definitions,
check the allowed axioms, and replay the solution in a fresh Lean kernel.
The solution module imports `Solution` and adds the exact conditional main, proved from the unconditional corollary. Challenge independently defines all five definitions and states main, both variants and the supplement. Their types and main's dependent definitions are checked by Comparator; source checks also match them to the FC files.

The upstream macOS development shim does not provide Linux sandboxing. For the
Linux command, set `COMPARATOR_LANDRUN` to the pinned Landrun binary and run:

```bash
bash scripts/compare.sh linux
```

The workflow has a quick independent-statement job and a complete-proof job.
The complete-proof job removes unused SDKs only on a GitHub-hosted ephemeral runner and provisions 8–16 GiB of swap while reserving 36 GiB of build disk. It requires 20 GiB free before the full comparison, records disk and memory every 30 seconds, and aborts below 4 GiB free so runner logs can still be saved. A separate control tests that this guard stops its own systemd unit. Only compressed Mathlib download archives are pruned after successful extraction; compiled dependencies and proof artifacts are preserved.
The latter obtains the trusted Mathlib cache and builds the checking tools;
the solution itself is built by the comparator within Landrun. The workflow
builds Landrun from its fixed commit, then runs the comparator as an
unprivileged user inside a transient systemd unit with AF_UNIX restricted.
Logs are uploaded under an artifact name containing the tested Git commit.
A small native Lake launcher outside the candidate's writable directory limits
sandboxed builds to two workers. It is compiled with the system C compiler;
the pinned Comparator source remains unchanged. Native code avoids requiring
shell-interpreter execution permissions inside Landrun.
Only the checking tools' build directories are cached between workflow runs.
The candidate's writable `.lake` directory starts fresh, and Mathlib artifacts
are downloaded from the official pinned cache before comparison. This prevents
a previous candidate build from changing the independent statement's next
checking environment. The comparator performs the full target/axiom/kernel
checks on each run.

## Intended rollout

1. Review the FC-style statement, unchanged PDF and root README locally.
2. Push the reviewed tree to the private `KitaKen1/ci-test-sandbox` repository and
   run `.github/workflows/lean.yml` there.
3. After the private run passes and its commit is reviewed, put the same source
   tree in `KitaKen1/simultaneous-primitive-roots` and run the same workflow.
4. Link the public run for the tested commit when documenting CI success.

Private testing is on `ci/simultaneous-primitive-roots-lean4331` in [ci-test-sandbox](https://github.com/KitaKen1/ci-test-sandbox/actions/runs/38768651954). Public results are listed in [the public workflow](https://github.com/KitaKen1/simultaneous-primitive-roots/actions/workflows/lean.yml).
The existing v4.35.0-rc3 evidence is historical evidence for the original
workspace, not evidence that the v4.33.1 publication build or CI passed.

See [STATUS.md](STATUS.md) for current local results.

The FC statements use the actual `FormalConjecturesUtil` import and
`category research solved, AMS 11` attributes. Their separate project in
`tools/fc-style/` pins the official FC revision and the same Mathlib/Lean 4.33.1.
The proof and Comparator projects continue to use the independent Mathlib-only Challenge.
The FC files include `[OAI26]` / `[Ki26]` references and `formal_proof using lean4 at "…"` attributes. Their URLs name the fixed proof-snapshot commit; the links become available when the prepared candidate is published.
