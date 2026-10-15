#!/usr/bin/env bash
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
component=${1:?Expected a component name}
[[ $component =~ ^[a-z0-9-]+$ ]] || { echo 'Invalid component name.' >&2; exit 2; }
[[ $(uname -s) == Linux ]] || { echo 'Component CI requires Linux.' >&2; exit 2; }
: "${COMPARATOR_LANDRUN:?Set COMPARATOR_LANDRUN to the pinned Linux landrun binary}"
[[ $COMPARATOR_LANDRUN != *fake-landrun* ]] || { echo 'Component CI requires real Landrun.' >&2; exit 2; }
python3 "$root/scripts/check_sources.py"
mkdir -p "$root/ci/results"
cd "$root/tools/comparator"
lake build comparator lean4export
tool_lean_path=$(lake env printenv LEAN_PATH)
# Both upstream executables have Main. Resolve the Comparator's Main explicitly.
export LEAN_PATH="$root/tools/comparator/.lake/build/lib/lean:$tool_lean_path"
export COMPARATOR_LEAN4EXPORT="$root/tools/lean4export/.lake/build/bin/lean4export"
cd "$root/lean"
lean_prefix=$(lean --print-prefix)
bounded_bin=$(bash "$root/scripts/prepare-comparator-runtime.sh")
export PATH="$bounded_bin:$PATH"
export LEAN_NUM_THREADS=2
driver="$root/ci/results/component-$component-driver.lean"
cp "$root/ci/build-component.lean" "$driver"
printf '\n#eval SPRComponentBuildHarness.run "comparator.json" "../ci/component-targets.json" "%s"\n' "$component" >> "$driver"
# The driver invokes the unchanged Comparator.safeLakeBuild for every target.
# Imported Main has its own entry point, so use #eval rather than --run.
bash "$root/scripts/run-linux-guarded.sh" "component-$component" "$lean_prefix/bin/lean" "$driver"
