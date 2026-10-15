# cadamcat/artin-primitive-roots-lean4 in this project

Source: https://github.com/cadamcat/artin-primitive-roots-lean4, commit
5a36d8670f4b56bf2bb15a3fb65ff4774f6caf27 (Apache-2.0; `vendor/ARTINPRIMITIVEROOTS_LICENSE`,
`vendor/ARTINPRIMITIVEROOTS_NOTICE`, `vendor/ARTINPRIMITIVEROOTS_THIRD_PARTY.md`). The checkout was
made by the project owner on 2026-10-12; a static audit before any build found no `sorry` other
than the placeholder of `Challenge.lean`, no axioms, no `native_decide` / `implemented_by` /
`unsafe`, no IO.

Vendored on 2026-10-12: the import closure of `ArtinPrimitiveRoots.Splitting.ZeroFree`, 1,021
modules under `vendor/ArtinPrimitiveRoots/`. (A first pass copied 992: the closure script missed
imports written as `import /- note -/ Module`; the remaining 29 were added the same day.)

* 1,004 files are byte-for-byte copies.
* 17 files under `ArtinPrimitiveRoots/Vendor/TauCeti/` are replaced by one-line forwarding modules
  `import TauCeti.X`. Upstream they are copies of TauCeti files declaring the same names; this
  project vendors TauCeti itself (commit d5a3709), and the 17 originals with their closure were
  added to `vendor/TauCeti` from that commit.

Vendored on 2026-10-12 (second batch): the import closure of `ArtinPrimitiveRoots.TypeII.MarkedTransfer`,
`ArtinPrimitiveRoots.TypeII.Rough`, `ArtinPrimitiveRoots.Construction.Proofs.C_TYPEII.UniformTransfer`
and `ArtinPrimitiveRoots.Construction.Proofs.C_TYPEII.Twisting` (570 modules, about 176,000 lines,
disjoint from the first batch). It contains the marked Type II criterion
(`TypeII.marked_coefficient_transfer`, [A] `lem:marked-coefficient-transfer`), its uniform form and
`TypeII.rough_type_ii` ([A] `prop:rough-type-ii`), for the supply side.

* 515 files are byte-for-byte copies.
* 55 files under `ArtinPrimitiveRoots/TypeII/Proofs/pp1/OAI/` are replaced by one-line forwarding
  modules `import OAI.NumberTheory.TwoPoint.X`. Upstream they are copies of the OpenAI files that
  differ only in a header comment and the import lines; this project vendors the originals.

Upstream targets Lean 4.34.1 and Mathlib d13f23b. Every edit made so that a file builds with this
project's Lean 4.35.0-rc3 and Mathlib f6090c7 is listed below.

## Edits

- `Splitting/Proofs/S7-EXT-HAD/Infrastructure/Analysis/Complex/ValueDistribution/LogCounting/Growth.lean`:
  the import `Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic` (renamed and split by
  Mathlib #42434) is replaced by `…Integrability.Log` and `…Integrability.PosLog`.
- `A1/Proofs/A1_BDATA/PrimeComplement.lean`: `set_option backward.isDefEq.respectTransparency false in`
  added before `prime_exponent_complement` (upstream sets only the `.types` sub-option; here instance
  synthesis for `ZMod p` with a let-bound `p` fails without it). Checked: the file then elaborates
  with no error.
- `Splitting/Proofs/S7-EXT-ARTIN/FractionalIdeals.lean` and `Hecke/Dictionary.lean`: one import line
  added, `import ClassFieldTheory.Compat.RayClassOfFinitePrimeExport`. Upstream these files use
  `ClassFieldTheory.finitePrimeFractionalIdeal_mem_primeTo`, which is private in ClassFieldTheory
  2eb22d6 and made public only by openai/math's patch. The new vendored module
  `vendor/ClassFieldTheory/Compat/RayClassOfFinitePrimeExport.lean` restates it publicly (same
  statement and proof). A scan of the 233 private declarations touched by openai/math's patches of
  ClassFieldTheory, AINTLIB and rellich-kondrachov found no other one mentioned by the vendored
  external or OpenAI code.
- `A1/Proofs/A1_LATTICE/UnitCompactCore.lean`, two places: the rewrite
  `WithZero.toAdd_unzero_eq_log _` directly after `WithZeroMulInt.toNNReal_neg_apply` is removed.
  In Mathlib f6090c7 `toNNReal_neg_apply` already states its right side with `WithZero.log`, so the
  second rewrite has nothing to rewrite.
- `Theta/Proofs/TH_COVER/SmallPowers.lean`, line 36 (`exists_sixthPowerNeighborhood`): the argument
  `(f := .ofClass (Valued.v : Valuation K ℤᵐ⁰))` of `MonoidWithZeroHom.ValueGroup₀.embedding` is
  written `(f := ((Valued.v : Valuation K ℤᵐ⁰) : K →*₀ ℤᵐ⁰))`. Mathlib #43728 states the value group
  of a valuation with the coercion `Valuation.toMonoidWithZeroHom` instead of
  `MonoidWithZeroHom.ofClass` (`Valued.mem_nhds` now gives `γ : (↑Valued.v).ValueGroup₀ˣ`); the two
  are equal by `rfl`, but the coercion `→*₀` to `→*` under `Units.map` no longer finds the old
  spelling. Checked: the file elaborates with no error.
- `Hecke/Theta/RayTheta.lean`: `set_option maxHeartbeats 5000000 in` added before the docstring of
  `rayThetaTail_le_heckeTheta_tail` (the declaration exceeds the default 200000 heartbeats at `whnf`
  here; the neighbouring declarations of the file already carry the same option). Checked: the file
  elaborates with no error.
- The same change of spelling (Mathlib #43728: `MonoidWithZeroHom.ofClass v` → the coercion
  `Valuation.toMonoidWithZeroHom v`, written `(v : K →*₀ Γ₀)`) at the other places where the library
  names the value group of `Valued.v`. In each case only the argument naming the homomorphism
  changes; the terms are equal by `rfl`. Except for `CongruenceTopology.lean` (same form as
  `SmallPowers.lean`), the affected part of each proof was copied into a scratch file over Mathlib
  alone and checked there to fail before the edit and to elaborate after it.
  - `Theta/Proofs/TH_COVER/CongruenceTopology.lean`, line 45: `(f := .ofClass (Valued.v : Valuation K
    (WithZero (Multiplicative ℤ))))` → `(f := ((Valued.v : Valuation K (WithZero (Multiplicative ℤ))) :
    K →*₀ WithZero (Multiplicative ℤ)))` (failed in round `zside-1` with the same message as
    `SmallPowers.lean`).
  - `A1/Characters.lean`, lines 137 and 268; `A2/Proofs/A2_FREQUENCY/ZfConvOpus/Conductor.lean`,
    line 79; `Proofs/qs_nq0_sol/Conductors.lean`, line 63: `(f := (.ofClass (Valued.v : Valuation L
    ℤᵐ⁰)))` → `(f := ((Valued.v : Valuation L ℤᵐ⁰) : L →*₀ ℤᵐ⁰))`.
  - `A2/Proofs/A2_WEIGHTS/Finite.lean`, line 25 (`exists_ball_subset_open_zero`) and
    `A1/Proofs/A1_FOURIER/LocalFourierTest.lean`, line 27 (`f_h_exists_ball_subset_open_zero`): in
    `let vf : … →*₀ … := MonoidWithZeroHom.ofClass (Valued.v : …)` the function
    `MonoidWithZeroHom.ofClass` is replaced by `Valuation.toMonoidWithZeroHom`.
  - `Theta/TorusInd.lean`, line 4481: `(f := .ofClass vHom)` → `(f := (vHom : K →*₀ WithZero
    (Multiplicative ℤ)))`.
  - `Theta/Proofs/TH_SMOOTH/FiniteHaar.lean`, lines 23–25 (`adicCompletion_secondCountable`), three
    places: `.ofClass q` → `(q : v.adicCompletion F →*₀ WithZero (Multiplicative ℤ))`. Without it the
    local instances `Countable (ValueGroup₀ (.ofClass q))ˣ` are not found for
    `Valued.hasBasis_uniformity`, which now asks for `Countable (↑Valued.v).ValueGroup₀ˣ`.
  - `Theta/LocalWhit.lean`, lines 96, 99, 100 (`wh_ball_subset_nhds`): `(f := (.ofClass (Valued.v :
    Valuation K _)))` → `(f := (Valuation.toMonoidWithZeroHom (Valued.v : Valuation K _)))`. (Here
    the ascription form `((Valued.v : Valuation K _) : K →*₀ _)` is not usable: with the value group
    left as `_` the `let` alone runs into the 200000 heartbeat limit at `whnf`; naming the
    projection, or writing both types out, elaborates at once. Checked on a scratch copy of the proof.)
- Redundant rewrite `WithZero.toAdd_unzero_eq_log _` directly after
  `WithZeroMulInt.toNNReal_neg_apply` removed (Mathlib #43589: `toNNReal_neg_apply` now gives
  `e ^ WithZero.log x`, so there is no `(WithZero.unzero _).toAdd` left to rewrite; the goal after the
  remaining rewrite is the goal the old pair produced). Same edit as in `UnitCompactCore.lean`,
  made before the files were first built, at the 16 places found by a scan of the unbuilt files:
  `A1/AddChar.lean` (`norm_embedding_eq_absNorm_zpow`); `A1/Proofs/A1_WEIL/HaarScale.lean` (`hqexp`);
  `A1/Proofs/A1_WEIL/w_f/Prelim.lean` (`absFin_toLoc_inv`); `A1/SLattice.lean` (`hqexp`, near line
  1576); `A2/Proofs/A2_WEIGHTS/Finite.lean` (`hqexp` near line 438, `hpow` near line 573);
  `Proofs/a2_bridges_impl2/FiniteRadial.lean` (`hqexp`); `Theta/Eis.lean` (`hπnorm` near line 3259,
  `hnorm` near line 5280); `Theta/LocalInt.lean` (near lines 320, 2349, 7390);
  `Theta/Proofs/TH_EIS_CONVERGE/FiniteApproximation.lean` (`hpow` near line 113, `hπnorm` near line
  374); `Theta/Proofs/TH_LOCAL_COEFF/UnitShell.lean` (`uniformizer_zpow_absFin`); `Theta/TorusInd.lean`
  (`hpowNN`, near line 4415).
- The same Mathlib change, where the proof goes on with `(WithZero.unzero h).toAdd`: one rewrite
  `← WithZero.toAdd_unzero_eq_log h` is added after `toNNReal_neg_apply`, which restores the old
  goal, in `A2/Proofs/A2_WEIGHTS/Finite.lean` (`thetaBall_absFin_bound`),
  `A1/Proofs/A1_FOURIER/LocalFourierTest.lean` (`f_h_thetaBall_abs_bound`) and
  `Proofs/a2_cond_b/AdditivePhase.lean` (`conductorUniformizer_norm`: `rw [htoAdd]` →
  `rw [← WithZero.toAdd_unzero_eq_log hval, htoAdd]`).
  Checked on scratch copies over Mathlib alone: `thetaBall_absFin_bound` and
  `conductorUniformizer_norm` after the edit, and five of the shapes of the previous entry,
  elaborate with no error.
- `A1/Proofs/A1_LAMBDA/CompletionNorm.lean`, `completionMap_valuation`: one line added before the
  final `exact`, `rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]`.
  Mathlib #41377 restated `HeightOneSpectrum.valuation_liesOver` with the exponent
  `w.asIdeal.ramificationIdx A` instead of `v.asIdeal.ramificationIdx' w.asIdeal`; the statement of
  `completionMap_valuation` (which keeps `ramificationIdx'`) is unchanged. Found by comparing the
  signatures of the Mathlib declarations the unbuilt files mention between the two revisions.
  Checked: the file up to `completionMap_integer_iff`, which uses Mathlib only, elaborates with no
  error after the edit.
- `OAI/NumberTheory/DirichletL/Eisenstein/CompactEnergyFamilies.lean`, line 241: `hK` → `hK.nullMeasurableSet` (Mathlib #42924).
- `OAI/NumberTheory/DirichletL/Eisenstein/CompactEnergyFamilies.lean`, line 236: `hK` → `hK.nullMeasurableSet` (Mathlib #42924).
- `Theta/TorusInd.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: unsolved goals).
- `ArtinPrimitiveRoots/Spec/Proofs/SPEC_RELLICH/orbitRestrictedMass_eq_indicator.lean`, line 151: `hS` → `hS.nullMeasurableSet` (Mathlib #42924).
- `Spec/Proofs/SPEC_RELLICH/localized_chart_H1_membership.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: failed to synthesize).
- `Theta/LocalInt.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: Type mismatch: After simplification, term).
- 2026-10-13 04:05 (main session, after loop `zside4` stopped on three files):
  `Spec/Proofs/SPEC_RELLICH/orbitRestrictedMass_eq_indicator.lean`, line 102: `MemLp.indicator hS (Lp.memLp u)`
  → `MemLp.indicator hS.nullMeasurableSet (Lp.memLp u)` (Mathlib #42924; the automatic fixer skips an
  identifier that is followed by further arguments).
  `Spec/Proofs/SPEC_RELLICH/localized_chart_H1_membership.lean`: `set_option synthInstance.maxHeartbeats 200000 in`
  added before the docstring of `localized_chart_H1_membership` (four `simp` calls timed out at the default
  20000 while synthesizing `MulActionSemiHomClass (… →ₙ+ ↥RellichC1c) …`). Statements unchanged.
  Not fixed yet: `Theta/LocalInt.lean` (five errors at lines 203, 343, 395, 4292, 6559; Haar-measure
  normalisation lemmas now simplify differently: `μ (𝒪_v) = ↑(addHaarScalarFactor …)` vs `1 = …`).
- 2026-10-13 (Codex, following the owner's request): all five remaining `Theta/LocalInt.lean`
  errors repaired, without changing any statement or adding an axiom.
  - `locHaar_regular`: rewrite `Measure.smul_apply`, `μ.norm_O`, and `hνO` explicitly before
    simplifying the scalar action. This avoids simplification rewriting the normalization
    equation in the wrong direction.
  - `localHaarFactor_eq_nnnorm`, `hfactorπinvForm`: explicitly rewrite the preimage identity
    and `μ.norm_O` in the Haar-character equation, instead of simplifying the entire equation.
  - The same theorem, `huval`: apply `map_mul` directly to the coerced units, avoiding the
    extra disjunction produced by unrestricted valuation simplification.
  - `spherical_shell_integral_unit_fixed`, `huInvVal`: use only `Units.val_inv_eq_inv_val`,
    `map_inv₀`, the unit valuation, and `inv_one`.
  - `completionResidueCenter_zero_mem_ball`: apply the inverse residue-field equivalence's
    injectivity and `map_zero`, retaining the existing `completionResidueClass_center` proof.
    This avoids unfolding the quotient algebra into a `FaithfulSMul` instance search.
  Verified: `LEAN_NUM_THREADS=2 lake build ArtinPrimitiveRoots.Theta.LocalInt` succeeds
  (10,240 jobs, no errors); log `verification/localint-20261013-build.log`.
- 2026-10-13 (Codex continuation): `Theta/Proofs/TH_LOCAL_COEFF/UnitShell.lean`,
  `completionResidueCenter_zero_mem_ball`: the same inverse-equivalence injectivity proof as
  `LocalInt.lean` replaces the broad simplification of `congrArg e hclass`. The original proof
  timed out while searching for `FaithfulSMul (𝓞 F)` on the completion's residue field (round 1,
  line 924). Statement unchanged. Verified in round 2: the module builds successfully (296s),
  log `verification/zside-20261013-full/build-02.log`.

- `Theta/LocalWhit.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: unsolved goals).
- 2026-10-13 (Codex continuation, manual repair after round 3): `Theta/LocalWhit.lean`:
  eliminate the definitional equality of the Weyl and original module structures before
  constructing the section-space linear maps, instead of rewriting that equality inside
  proofs whose subtype arguments depend on the module instance. In `hshiftG`, use
  `map_mul` and `mul_assoc` directly. Remove the final `rfl` after the `shellVec`
  simplification already closes `hu`. The first manual build eliminated the four
  round-3 errors and reported only a remaining reference to the eliminated `hModule`;
  that reference is removed as well. Statements unchanged. The first manual build is
  recorded in `verification/zside-20261013-full/localwhit-manual-01.log`.
  Verified: the final source builds successfully in round 4 (1032s including
  waiting for a compiler slot), `verification/zside-20261013-full/build-04.log`.
- `Theta/Proofs/TH_EIS_WHIT/GoodFactor.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: Type mismatch: After simplification, term).
- `Theta/Proofs/TH_EIS_WHIT/SphericalBound.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: Type mismatch: After simplification, term).

- 2026-10-13 (Codex continuation): `A2/Proofs/A2-QS-CANCEL/C3/Estimate.lean`:
  replace the import of `C3.Decomp` by the real-power module and the six Mathlib
  tactic modules the file uses. Its declarations and proofs are unchanged and
  mention only real arithmetic. The only consumer, `C3.TransBound`, already
  imports `C3.Trans`, which imports `C3.Decomp`; it retains the number-field
  declarations it needs. A profile of the old build showed `Lean.finalizeImport`
  comparing imported environments for over twenty minutes. The narrower
  import was checked successfully on an exact scratch copy of the updated
  source. The axiom check of `E3_estimate` reports only `propext`,
  `Classical.choice`, and `Quot.sound`;
  log `verification/zside-20261013-full/estimate-narrow-01.log`.
  The old import's already-running round-6 compilation also completed (1805s);
  round 7 refreshed the actual module artifact successfully in 18s.
- 2026-10-13 (Codex continuation): `Hecke/Boundary.lean`: update the stale
  comments about a `sorry` placeholder to describe the existing forwarding
  proof from `ArtinPrimitiveRoots.A2.thm_hecke_zero_free`. Documentation only;
  declarations and proofs unchanged. The full boundary's kernel axiom check
  remains part of the Z-side bridge validation.
- `Theta/Proofs/TH_NONZERO/sphWeyl_lam_zero.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: Type mismatch: After simplification, term).

- 2026-10-13 (Codex continuation): `Proofs/th_res_whit_b/ComplexArch.lean`:
  import `Theta.LocalInt` directly instead of `TH_RES_WHIT.Defs`; remove the
  unused global number-field variable declarations. The file uses only local
  complex spherical sections and Jacquet integrals, and no `AnalyticFamily`
  or `ContinuedEis`. Declaration statements and proof bodies are unchanged.
  An exact-source probe compiled successfully and checked both exported
  Jacquet theorems: only `propext`, `Classical.choice`, and `Quot.sound`.
  Log: `verification/zside-20261013-full/complexarch-narrow-01.log`.
  The already-running round-7 build of the old import also succeeded; a
  later root build will refresh that artifact from the narrower source.
- 2026-10-13 (Codex continuation): `Proofs/th_res_whit_b/ComplexBesselPos.lean`:
  remove the unused import of `ComplexArch`. Its Bessel definitions and
  Schlafli identity are supplied by the retained `Theta.Shared` import. The
  only consumer, `SectionMatch`, imports `ComplexArch` separately. Statement
  and proofs unchanged. The exact-source probe compiled successfully, and
  `besselK_oneThird_pos` depends only on `propext`, `Classical.choice`, and
  `Quot.sound`. Log: `verification/zside-20261013-full/besselpos-narrow-01.log`.
- `Proofs/th_continue_b/ThetaBasics.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: maximum recursion depth has been reached).
- `Theta/Proofs/TH_RES_FOURIER/constantCell_finite_analytic.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: Type mismatch: After simplification, term).
- 2026-10-13 18:07 (zport2 agent): `Proofs/th_continue_b/ThetaBasics.lean`:
  (a) the file-level `set_option backward.isDefEq.respectTransparency false` that the automatic
  fixer had inserted after the import is removed again (the file is back to the upstream header).
  It did not repair the error and created a second one: with it, `simp [hv]` in
  `continuedEis_rootRep_compF` (line 303) also ran out of the file's `maxRecDepth 128`.
  (b) `set_option maxRecDepth 256 in` added before `theorem continuedEis_archRep_compF`: its
  `simpa [hv] using hF v` (old line 420) exceeds the file-level `set_option maxRecDepth 128` under
  this Mathlib; 256 (still below Lean's default 512) is enough. Statements and proofs unchanged.
  Checked first on a scratch copy of the two theorems (128 fails, 256 and 512 pass; the first
  theorem passes at 128 without the transparency option), then
  `lake build ArtinPrimitiveRoots.Proofs.th_continue_b.ThetaBasics` succeeds (10552 jobs, 83s).
- `Proofs/th_continue_b/TorusRootReduction.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: maximum recursion depth has been reached).
- 2026-10-13 18:19 (zport2 agent): `Proofs/th_continue_b/TorusRootReduction.lean`,
  `continuedEis_theta_torus_root_local_reduction`: `set_option maxRecDepth 256 in` added before the
  theorem. `exact hy ⟨v, hv⟩` (line 103) ran out of the file-level `set_option maxRecDepth 128`
  (loop `zside7`, round 1). The file-level `set_option backward.isDefEq.respectTransparency false`
  that the automatic fixer inserted after round 1 did not change the error (round 2) and is removed
  again, so the header is the upstream one. Statement and proof unchanged. Checked:
  `lake build ArtinPrimitiveRoots.Proofs.th_continue_b.TorusRootReduction` succeeds (92s).
- `Theta/Proofs/TH_FAMILY_FIELDS/thetaN_fields.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: 'simp' made no progress).
- `A2/Proofs/A2_EULER/Parts/e_f/LocalSectors.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: failed to synthesize).
- `A2/Proofs/A2_PROBE/Lead/pr_b/PeriodicPoissonProof.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: failed to synthesize).
- 2026-10-13 20:48 (zport2 agent, after loop `zside8` stopped): three files whose `map_add` /
  `map_sub` / `map_nsmul` rewrites on `Ideal.Quotient.mk (Ideal.span {…}) : ↥S.R →+* ↥S.R ⧸ _` failed
  with "failed to synthesize AddHomClass/AddMonoidHomClass (↥S.R →+* ↥S.R ⧸ Ideal.span {…}) ?m ?m …
  (deterministic) timeout at `typeclass`, maximum number of heartbeats (20000)" (and, nested,
  `Module Q ↥S.R`). Fix in all three: `set_option synthInstance.maxHeartbeats 200000 in` before the
  declaration (kind 4); statements and proof texts unchanged.
  - `A2/Proofs/A2_EULER/Parts/e_f/LocalSectors.lean`: before `theorem po_C_local_values`
    (three `simp [δ]` at lines 2385, 3001, 3442 of the upstream text). The file-level
    `set_option backward.isDefEq.respectTransparency false` that the automatic fixer inserted after
    round 2 (previous entry of this log) is removed again: it did not cure the timeouts and produced
    two new errors (1592:4 and 1997:8, "Type mismatch: After simplification"). Header is upstream.
  - `A2/Proofs/A2_PROBE/Lead/pr_b/PeriodicPoissonProof.lean`: before
    `noncomputable def residueCosetEquiv` (`rw [map_add]` line 37, `rw [map_sub, …]` line 58) and
    before `theorem additivePhase_norm_one` (`map_nsmul qmk …` line 134). The fixer's file-level
    transparency option (previous entry) is removed again: with it the line-37 timeout remained.
    Header is upstream.
  - `A2/Proofs/A2_EULER/Parts/e_c/LocalNormalization.lean`: before
    `theorem first_multiplier_congruence` and `theorem second_multiplier_congruence`
    (`simp only [map_sub, map_mul, Ideal.Quotient.mk_out]`, lines 179 and 212). The file-level
    transparency option in this file is upstream and untouched.
  Verified: `lake build` of the three modules together succeeds (11288 jobs; PeriodicPoissonProof
  125s, LocalSectors 141s, LocalNormalization 60s), log `scratchpad/zport2_agent/z3-build-1.log`.
- `A2/Poisson/Missing.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: failed to synthesize).
- 2026-10-13 21:09 (zport2 agent, after loop `zside9` stopped): `A2/Poisson/Missing.lean`: the same
  instance-synthesis timeouts (default 20000) as in the previous entry, on `Module Q ↥S.R` (line
  2800, `map_nsmul qMap q x`) and on `AddHomClass/AddMonoidHomClass (↥S.R →+* ↥S.R ⧸ Ideal.span {…})
  ?m ?m` (lines 3566, 7078, 7694, 8135). `set_option synthInstance.maxHeartbeats 200000 in` added
  before `private theorem po_e_residue_norm_one` and `private theorem po_residue_addPhase_sum`
  (in both cases above the existing `set_option maxHeartbeats … in`) and before
  `theorem po_C_local_values`. The file-level `set_option backward.isDefEq.respectTransparency false`
  that the automatic fixer inserted after round 1 (previous line of this log) is removed again: with
  it four of the five timeouts remained and five new errors appeared (1557:62, 3373:60, 4147:60
  unsolved goals; 6286:4, 6690:8 type mismatch). Header is upstream; statements and proof texts
  unchanged. Verified: `lake build ArtinPrimitiveRoots.A2.Poisson.Missing` succeeds (11367 jobs,
  179s), log `scratchpad/zport2_agent/poissonmissing-build-1.log`.
- `ArtinPrimitiveRoots/TypeII/Proofs/pd1c/Goodness.lean`, line 653: `hAm.nullMeasurableSet` → `hAm.nullMeasurableSet.nullMeasurableSet` (Mathlib #42924).
- `ArtinPrimitiveRoots/TypeII/Proofs/pd1c/Goodness.lean`, line 574: `hAm.nullMeasurableSet` → `hAm.nullMeasurableSet.nullMeasurableSet` (Mathlib #42924).
- 2026-10-14 00:50 (zport2 agent) CORRECTION of the two lines above. The edit of
  `TypeII/Proofs/pd1c/Goodness.lean` is: lines 574 and 653, `rw [integrableOn_indicator_iff hAm]` →
  `rw [integrableOn_indicator_iff hAm.nullMeasurableSet]` (Mathlib #42924; in
  `pd1c_goodTestTwoBadWeight_intervalIntegrable` and in the `hInt` step of the next lemma). I made
  this edit by hand at 00:37 while round 1 of loop `typeii1` was finishing; at 00:38 the automatic
  fixer applied the same suffix a second time (its idempotence check did not recognise an
  already-suffixed identifier), giving `hAm.nullMeasurableSet.nullMeasurableSet`, which is what the
  two lines above record. The duplicate was removed again at 00:48; the file now differs from the
  upstream text only by the single suffix at the two sites. The fixer has a guard against this now
  (`scratchpad/fix_nullmeasurable.py`, backup `.bak-20261014-0050`). Verification: first job of
  loop `typeii2`.
- `TypeII/PD/RootReplacement.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: Type mismatch: After simplification, term).
- `Proofs/pd_life_b/BirthCombinatorics.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: Type mismatch: After simplification, term).
- `TypeII/Proofs/pd4c/Geometry.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: ring failed, ring expressions not equal).
- `TypeII/Proofs/pd6b/EdgeCoordinates.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: Type mismatch: After simplification, term).
- `TypeII/PD/MemoryResults.lean`: file-level `set_option backward.isDefEq.respectTransparency false` inserted after the imports (first error: Type mismatch: After simplification, term).
- 2026-10-14 02:52 (zport2 agent, after loop `typeii2` stopped): `TypeII/PD/MemoryResults.lean`:
  `set_option backward.isDefEq.respectTransparency false in` added before
  `private theorem projLine_eq_of_det_dvd`. Its `simpa [hz2] using hdetmod` (upstream line 2433)
  failed with "Type mismatch: After simplification, term hdetmod has type ↑z.1 * ↑z'.2 - 0 = 0 but
  is expected to have type ↑z.1 = 0 ∨ ↑z'.2 = 0" (`sub_zero` no longer fires in `ZMod p` under the
  default transparency). The file-level option that the automatic fixer inserted after round 3
  (previous line of this log) is removed again: it repaired this theorem but broke two others
  (2529:19 and 7764:72 "unsolved goals" in round 4), so the option is now limited to the one
  declaration that needs it. Header is upstream; statement and proof text unchanged. Verified:
  `lake build ArtinPrimitiveRoots.TypeII.PD.MemoryResults` succeeds (9491 jobs, 113s), log
  `scratchpad/zport2_agent/memoryresults-build-1.log`.
