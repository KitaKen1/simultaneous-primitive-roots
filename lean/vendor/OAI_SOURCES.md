# Vendored OpenAI Lean sources

Source: https://github.com/openai/math, commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, directory `lean/` (Apache-2.0, see `OAI_LICENSE`).
A reference checkout of the directories used is kept outside the build at `~/.cache/lean-builds/openai-math` (sparse, pinned to the commit above).
Files are copied unchanged, at the same relative path; a modification, if one is ever needed, must be marked in the file with `Vendoring fix`.

| Date | Root modules | Files | Purpose |
|---|---|---:|---|
| 2026-10-11 | `OAI.NumberTheory.PrimeGaps.Main` | 48 | Siegel–Walfisz, Bombieri–Vinogradov, additive and multiplicative large sieve |
| 2026-10-12 | `OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLargeValues`, `OAI.NumberTheory.TwoPoint.Halasz.HalaszLogPhase` | 111 | Dirichlet polynomial mean squares (`mrt_dirichlet_mean_square`, `mrt_dirichlet_separated_samples`), logarithmic phases (`halasz_log_phase_bound`): [P] Lemma 2.2, 2.4 |
| 2026-10-12 | `OAI.NumberTheory.TwoPoint.Halasz.HalaszWeakHurwitzTheorem`, `OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakVKStrip` | 78 more (185 in the closure) | weak Vinogradov–Korobov zero-free strip and `L'/L` bound for Dirichlet `L`-functions (`mrt_weak_hurwitz_growth`, `MRTWeakHurwitzGrowthInput.strip_logderiv`): [P] Lemma 2.3 |
| 2026-10-12 | `PrimeNumberTheoremAnd.Erdos970.*`, `StrongPNT.Erdos970.*` (extracted from `lean/patches/PrimeNumberTheoremAnd-lean4341.patch` and `StrongPNT-lean4341.patch`: the new files only) | 20 + 8 | Mertens, zeta bounds, zero-free region, strong PNT; dependencies of the weak VK and zero-density files |
| 2026-10-12 | `OAI.NumberTheory.Jacobsthal.Estimates.FundamentalBlockEstimate`, `OAI.NumberTheory.Jacobsthal.Sieve.EulerProductRatio` | 53 | Brun–Hooley block sieve / fundamental lemma (`fundamental_integer_parameter`, `finite_small_sieve_bound`): [P] Lemma 2.5–2.6 (rough counts, block sieve), [S] Lemma 2.9 |
| 2026-10-12 | `OAI.NumberTheory.JointDickman.Arithmetic.PrimeIntervalSums`, `…MertensDischarge` | 6 | reciprocal sums of primes in `(x^α, x^β]` (`largePrimeSet_reciprocal_tendsto`), Mertens input |
| 2026-10-12 | `OAI.NumberTheory.EgyptianFractions.VaughanNearRational` | 4 | bilinear estimate near rationals (`near_rational_interval_bilinear_sq_le`): [S] Lemma 4.2 |

Removed again on 2026-10-12: `OAI.NumberTheory.TotientAsymptotic.{UniformPrimePairBound,ShiftedPrimePairBound}` (64 files) and the three PrimeNumberTheoremAnd Selberg sieve files. The dependency map `docs/s-side-map.md` shows that the prime-pair bounds are not on the path to `FixedClassLongPrimeStatistic`.

## rellich-kondrachov (vendor/RellichKondrachov, 15 files)

Source: the module-system port of `abenenson/rellich-kondrachov` (Adam Benenson, Apache-2.0, licence
copy in `vendor/RELLICHKONDRACHOV_LICENSE`) carried by LeanPool, `LeanPool/RellichKondrachov/`,
lean-pool commit 01db1d7 (local clean checkout, Lean 4.35.0-rc3, Mathlib c55e6e7). The import
closure of `Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich` (15 files, 4,020 lines) was copied
with the import prefix `LeanPool.RellichKondrachov.` renamed back to the upstream `RellichKondrachov.`
so that `OAI.NumberTheory.DirichletL.CubicSieve.RadialWindows` imports it unchanged.

Edits for Mathlib f6090c7 (`memLp_indicator_iff_restrict` and
`eLpNorm_indicator_eq_eLpNorm_restrict` now take `NullMeasurableSet`): `hs` →
`hs.nullMeasurableSet` at three places in `MeasureTheory/Function/LpSpace/Restrict.lean`, and
`hKm` → `hKm.nullMeasurableSet` at two places in `.../L2Compactness/Smoothing.lean`.
In `.../Euclidean/Rellich.lean`, three elaboration fixes that only supply an argument the
elaborator no longer infers here: `norm_nonneg _` → `norm_nonneg (h1ToL2 …)` (line 110), and
`mem_closedBall_zero_iff.mp hx` → `(mem_closedBall_zero_iff (a := x)).mp hx` (two places).

## TauCeti additions for the Hecke zero-free closure (27 files)

Source: TauCeti commit d5a3709 (local clean checkout), the same revision as the files already in
`vendor/TauCeti`; the 31 files of the closure that were already vendored are byte-identical to it.
The 27 new files are the rest of the import closure of the 23 TauCeti modules that
`cadamcat/artin-primitive-roots-lean4` imports (local fields, adeles and ideles, Henselian rings,
roots of unity, discriminants). Copied unchanged.

## PrimeNumberTheoremAnd/SmoothExistence.lean (compatibility module, own file)

`cadamcat/artin-primitive-roots-lean4` imports `PrimeNumberTheoremAnd.SmoothExistence` for the
root-level `smooth_urysohn_support_Ioo`. openai/math's patch reduces the upstream file to that one
declaration. The vendored file restates it (statement copied from the patch) and proves it by the
vendored `Erdos970.smooth_urysohn_support_Ioo`.

## Edits to vendored OpenAI files for Mathlib f6090c7

The vendored `OAI/` files are byte-identical to openai/math fd4aeeb except for the following.

- `OAI/NumberTheory/TwoPoint/Halasz/HalaszCircleWindow.lean`, line 20: `measurableSet_closedBall`
  → `measurableSet_closedBall.nullMeasurableSet` (`MemLp.indicator` now takes a
  `NullMeasurableSet`; found by the build of 2026-10-12).
- `OAI/NumberTheory/DirichletL/CubicSieve/FrequencyBlocks.lean`, lines 475–478: the element of a
  multi-line set literal `{a *⏎ b *⏎ c}` is wrapped in parentheses. Under Lean 4.35.0-rc3 the
  unparenthesized form fails to parse (`unexpected token '}'; expected '|'`) when the continuation
  lines are indented to the left of the opening brace; on one line it parses.
- `OAI/NumberTheory/TwoPoint/Halasz/HalaszTorusWindow.lean`, line 28: `.nullMeasurableSet` appended
  (same `MemLp.indicator` change).
- `OAI/NumberTheory/Jacobsthal/Sieve/EulerProductRatio.lean`: `set_option maxHeartbeats 1600000 in`
  before `int_mem_primeResidueSet` (its `change` step exceeds the default 200000 here).
- `PrimeNumberTheoremAnd/Erdos970/MertensClassical.lean`: the import
  `Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic` was renamed and split by Mathlib
  (#42434); replaced by `…Integrability.Log` and `…Integrability.PosLog`.
  Line 1129: `integrableOn_indicator_iff measurableSet_Ici` → `… measurableSet_Ici.nullMeasurableSet`.
- Multi-line set literals, the same parse change as in `FrequencyBlocks.lean` above: under Lean
  4.35.0-rc3 an application argument inside `{…}` must start to the right of the opening brace, so
  `Ideal.span {f a⏎ b}` with the continuation line indented further left fails with
  `unexpected token '}'; expected '|'`. The element is wrapped in parentheses, `{(f a⏎ b)}`, at
  eight places (found by the build of `CubicSieve/GlobalEncoding.lean` on 2026-10-12 and by a scan of
  the unbuilt files of the closure of `ArtinPrimitiveRoots.Splitting.ZeroFree`; each original was
  confirmed to fail to parse with its lines copied into a scratch file, and `GlobalEncoding.lean`
  was checked to elaborate with no error after the edit):
  `OAI/NumberTheory/DirichletL/CubicSieve/GlobalEncoding.lean` lines 502–503 (`globalSecondFixedTriple`);
  `…/Eisenstein/SmoothTests.lean` lines 553–554 (`cubeParityKey`);
  `…/GaussSum/ActiveReindexing.lean` lines 411–412 (`activeModelPrimeEquiv_span`; statement changed
  in its source text only: the literal is in the lemma's statement, and the parentheses do not
  change the elaborated type);
  `…/RowCompletion/BranchDecoding.lean` lines 266–267;
  `…/RowCompletion/ReflectedFibers.lean` lines 263–264, 299–300, 303–304, 676–677.
  Not changed: `…/RowCompletion/BranchDecoding.lean` line 550, where the line break is inside
  parentheses and the literal parses as it is.

## LeanPool SelbergSieve4: structure renamed (2026-10-12)

`vendor/LeanPool/SelbergSieve4/Selberg.lean` declared a root-level structure `SelbergSieve`, the same
name as the structure in `Mathlib.NumberTheory.SelbergSieve`, so no file could import both (17
clashing constants: the structure, its fields `level`, `one_le_level` and the generated
recursors). The structure and its namespace are renamed to `LPSelbergSieve` in `Selberg.lean` and
`Applications/PrimeCountingUpperBound.lean`; the three consumers
`SimultaneousPrimitiveRoots/{ProgressionSelbergSieve,ProgressionSelbergDenominator,RealProgressionSieve}.lean`
are updated. A scan of all 41,800 constants declared outside Mathlib in the closure of the two
project roots against the whole of Mathlib (`verification/clash-hits.tsv`) found no other clash:
the remaining 8 hits are generated `.eq_1` / `.congr_simp` lemmas of Mathlib definitions, and 7
are `Lake.Util.Casing` itself.

## AINTLIB DedekindResidue (vendor/DedekindResidue, 14 files) and one more ClassFieldTheory file

Fetched on 2026-10-12 with the project owner's permission into `~/.cache/lean-builds/ext-deps/`
(blobless, sparse clones at the pinned commits):

* `CBirkbeck/AINTLIB` at 160e446617a2168c34c95bbe7a76c4105b392434, `projects/DedekindResidue`.
  Vendored: the import closure of `DedekindResidue.CompletedZeta.{ClassTheta, Existence,
  FunctionalEquation, MellinAgreement}` (14 files, 6,849 lines, Mathlib only), after applying the
  `CompletedZeta` hunks of openai/math's `lean/patches/AINTLIB-lean4341.patch` (they modify
  `Existence`, `FunctionalEquation`, `HeckeTheta`, `MellinAgreement`, `PoissonLattice`,
  `PoissonSummation`, `ThetaEstimates`, `ThetaLattice`; the patch applied cleanly). Library options
  as in AINTLIB's lakefile. A static audit of the 14 files found no `sorry`, axiom, `native_decide`,
  metaprogram or IO.
* `n-yamaguchi-0729/ClassFieldTheory` at 2eb22d6485af45f29c5219de6c49f196a61c4f49, `Lean4/`.
  Vendored: `ClassFieldTheory/Theorems/ConductorsAndRayClassFields/RayClassGroupFinite.lean`
  (unmodified). The rest of its import closure (941 files) was already vendored; 903 of those are
  byte-identical to the fetched commit and 38 carry this project's earlier edits for Lean
  4.35.0-rc3. openai/math's `ClassFieldTheory-lean4341.patch` is NOT applied to the vendored
  ClassFieldTheory; it touches 24 files of the closure that `cadamcat/artin-primitive-roots-lean4`
  uses, so differences may surface when that code is built.

Edits for this toolchain: (listed here as they are made)

