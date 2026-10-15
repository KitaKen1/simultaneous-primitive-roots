import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.upstairs_rhp_euler_identity
import SimultaneousPrimitiveRoots.Unconditional.AbelianFactorization

/-!
# From ray Hecke zero-free continuations to cyclotomic abelian zeta factorization

The Artin map and the analytic Euler correction are supplied by the vendored abelian
Euler factorization. The only input below is the ray Hecke zero-free continuation
statement, with an arbitrary width. `ExternalHecke.lean` discharges that input with
the vendored Hecke theorem at width `10⁻⁶`.

Keeping this adapter separate allows its proof to be checked independently of the
Hecke zero-free theorem's build. This file belongs to the final non-module layer.
-/

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional

open NumberField ClassFieldTheory ArtinPrimitiveRoots.Hecke ArtinPrimitiveRoots.Splitting

/-- The actual abelian Euler identity converts zero-free ray Hecke continuations into
the zeta factorization consumed by the Kummer descent. -/
theorem cyclotomicAbelianZetaFactorization_of_rayHeckeZeroFree {δ : ℝ}
    (hHecke : ∀ (n : ℕ) [NeZero n], 12 ∣ n →
      ∀ (m : RayClassModulus (CyclotomicField n ℚ)) (η : RayClassGroup m →* ℂˣ),
        ∃ (U : Set ℂ) (Λ : ℂ → ℂ), IsOpen U ∧ {s : ℂ | 1 - δ < s.re} ⊆ U ∧
          MeromorphicOn Λ U ∧ (∀ s : ℂ, 1 < s.re → Λ s = LSeriesRay η s) ∧
          ∀ s : ℂ, 1 - δ < s.re → meromorphicOrderAt Λ s ≤ 0) :
    CyclotomicAbelianZetaFactorization δ := by
  intro n _ h12 L _ _ _ _
  classical
  obtain ⟨m, Art, -, -, hE, hEne, hEuler⟩ :=
    upstairs_rhp_euler_identity (CyclotomicField n ℚ) L
  have hΛ := fun χ : (L ≃ₐ[CyclotomicField n ℚ] L) →* ℂˣ =>
    hHecke n h12 m (χ.comp Art)
  choose U Λ _ hUs hΛm hΛe hΛo using hΛ
  refine ⟨_, Finset.univ, s7UpstairsCorrection (CyclotomicField n ℚ) L m, Λ,
    ?_, hEne, ?_, ?_, ?_⟩
  · intro s hs
    exact hE.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  · intro χ _
    exact (hΛm χ).mono_set (hUs χ)
  · intro χ _ s hs
    exact hΛo χ s hs
  · intro s hs
    rw [hEuler s hs]
    congr 1
    exact Finset.prod_congr rfl fun χ _ => (hΛe χ s hs).symm

end SimultaneousPrimitiveRoots.Unconditional
