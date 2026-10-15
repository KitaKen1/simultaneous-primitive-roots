import ArtinPrimitiveRoots.Hecke.Boundary
import SimultaneousPrimitiveRootsFinal.CyclotomicEulerBridge

/-!
# [A, Theorem 1.2] from the vendored formalization, in the form this project consumes

The vendored `ArtinPrimitiveRoots` library (cadamcat/artin-primitive-roots-lean4) proves

* `ArtinPrimitiveRoots.HeckeBoundary.thm_hecke_zero_free`: [A, Theorem 1.2] for the ray class
  characters of `CyclotomicField n ℚ`, `12 ∣ n`, with meromorphic orders;
* `ArtinPrimitiveRoots.Splitting.upstairs_rhp_euler_identity`: for every abelian extension `T / B`
  of number fields, `ζ_T = E * ∏_χ L(χ ∘ Art)` on `Re s > 1` with an Artin map `Art` on a ray class
  group and a finite Euler correction `E`, analytic and nonvanishing on `Re s > 0`.

Together they are `CyclotomicAbelianZetaFactorization δ₀` (`δ₀ = 10⁻⁶`), the Mathlib-level
hypothesis of `AbelianFactorization.lean`. Hence `AllKummerZetaZeroFree δ₀`, and `MainClaim`
follows from the public paper's `prop:ap` alone.

This file is not a `module`: the vendored library is not.
-/

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional

open ArtinPrimitiveRoots ArtinPrimitiveRoots.Hecke ArtinPrimitiveRoots.HeckeBoundary
  ArtinPrimitiveRoots.Splitting ClassFieldTheory

/-- **The zero-free factorization of `ζ_L`, from the vendored formalization of [A].** -/
theorem cyclotomicAbelianZetaFactorization_δ₀ : CyclotomicAbelianZetaFactorization δ₀ := by
  exact cyclotomicAbelianZetaFactorization_of_rayHeckeZeroFree (δ := δ₀)
    thm_hecke_zero_free

theorem δ₀_eq : δ₀ = (10 : ℝ)⁻¹ ^ 6 := by
  norm_num [δ₀]

/-- The same factorization with the project's numerical width. -/
theorem cyclotomicAbelianZetaFactorization :
    CyclotomicAbelianZetaFactorization ((10 : ℝ)⁻¹ ^ 6) := by
  rw [← δ₀_eq]
  exact cyclotomicAbelianZetaFactorization_δ₀

/-- **[A, Lemma `spl:field-bounds`], with no hypothesis**: `(s - 1) ζ_{K_q}` has no zeros in
`Re s > 1 - 10⁻⁶`, for every `a ≥ 2` and every prime `q > a`. -/
theorem allKummerZetaZeroFree : AllKummerZetaZeroFree ((10 : ℝ)⁻¹ ^ 6) := by
  rw [← δ₀_eq]
  exact allKummerZetaZeroFree_of_factorization (by norm_num [δ₀])
    cyclotomicAbelianZetaFactorization_δ₀

/-- **`MainClaim` from the public paper's `prop:ap` alone** (the Hecke side is a theorem). -/
theorem mainClaim_of_longPrimeStatistic
    (hstat : FixedClassLongPrimeStatistic (1 - (10 : ℝ)⁻¹ ^ 6 / 2) (1 - (10 : ℝ)⁻¹ ^ 6 / 4)) :
    MainClaim :=
  mainClaim_of_paperParameters_and_factorization hstat
    (by rw [← δ₀_eq]; exact cyclotomicAbelianZetaFactorization_δ₀)

end SimultaneousPrimitiveRoots.Unconditional
