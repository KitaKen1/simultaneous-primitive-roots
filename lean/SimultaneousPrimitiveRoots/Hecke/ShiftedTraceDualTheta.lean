module

public import SimultaneousPrimitiveRoots.Hecke.ShiftedTheta
public import SimultaneousPrimitiveRoots.Hecke.TraceDualTheta

/-!
# Hecke's theta transformation for a coset `α₀ + ℤ b` of a number field lattice

Let `b` be a `ℚ`-basis of the number field `K`, `b^∨ = b.traceDual`, and `α₀ ∈ K` with
coordinates `v = b.repr α₀`. For positive weights `w_σ` invariant under complex conjugation and
`t > 0`,

`∑_{m ∈ ℤ^n} exp(-π t Q_w(∑ m_j b_j + α₀))
  = |det|⁻¹ t^{-n/2} ∑_{n ∈ ℤ^n} e(n·v) exp(-π Q_{1/w}(∑ n_j b^∨_j) / t)`

(`tsum_traceDual_theta_shift`), where `e(n·v) = charPi n (-v)`.

This is the theta transformation for a shifted lattice (`tsum_shiftedGaussian_eq`) in the
Hartley coordinates of `TraceDualTheta.lean`. It is the input for the continuation of the partial
zeta functions of ray classes: the elements `α ≡ 1 (mod 𝔪)` of an ideal `𝔟` prime to `𝔪` form a
coset `α₀ + 𝔟𝔪` (step Z2 of `docs/unconditional-roadmap.md`).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField NumberField.ComplexEmbedding Complex Matrix
open scoped Real ComplexConjugate

variable {K : Type*} [Field K] [NumberField K]

/-- The Hartley coordinates are additive. -/
theorem casCoord_add (w : (K →+* ℂ) → ℝ) (x y : K) (σ : K →+* ℂ) :
    casCoord w (x + y) σ = casCoord w x σ + casCoord w y σ := by
  unfold casCoord
  rw [map_add, Complex.add_re, Complex.add_im]
  ring

/-- The Hartley coordinates are `ℚ`-linear. -/
theorem casCoord_sum_qsmul {ι : Type*} [Fintype ι] (w : (K →+* ℂ) → ℝ) (b : ι → K)
    (q : ι → ℚ) (σ : K →+* ℂ) :
    casCoord w (∑ j, q j • b j) σ = ∑ j, (q j : ℝ) * casCoord w (b j) σ := by
  unfold casCoord
  have hσ : ∀ j, σ (q j • b j) = ((q j : ℝ) : ℂ) * σ (b j) := by
    intro j
    rw [Rat.smul_def, map_mul, map_ratCast]
    push_cast
    ring
  have hre : (σ (∑ j, q j • b j)).re = ∑ j, (q j : ℝ) * (σ (b j)).re := by
    rw [map_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hσ j, Complex.re_ofReal_mul]
  have him : (σ (∑ j, q j • b j)).im = ∑ j, (q j : ℝ) * (σ (b j)).im := by
    rw [map_sum, Complex.im_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hσ j, Complex.im_ofReal_mul]
  rw [hre, him, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real coordinate vector of `α₀` in the basis `b`. -/
def basisCoords (b : Module.Basis ι ℚ K) (α₀ : K) : ι → ℝ := fun j => ((b.repr α₀ j : ℚ) : ℝ)

omit [DecidableEq ι] in
/-- The Hartley coordinates of a coset point. -/
theorem casMatrix_mulVec_shift (w : (K →+* ℂ) → ℝ) (b : Module.Basis ι ℚ K)
    (e : ι ≃ (K →+* ℂ)) (m : ι → ℤ) (α₀ : K) (i : ι) :
    (casMatrix w b e *ᵥ (intVec m + basisCoords b α₀)) i =
      casCoord w (∑ j, m j • b j + α₀) (e i) := by
  rw [Matrix.mulVec_add, Pi.add_apply, casMatrix_mulVec_intVec, casCoord_add]
  congr 1
  have hrepr : α₀ = ∑ j, b.repr α₀ j • b j := (b.sum_repr α₀).symm
  conv_rhs => rw [hrepr]
  rw [casCoord_sum_qsmul]
  simp only [Matrix.mulVec, dotProduct, casMatrix, basisCoords]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq ι] in
/-- The squared length of a coset point in Hartley coordinates is the weighted norm form. -/
theorem sqNorm_casMatrix_mulVec_shift (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ))
    {w : (K →+* ℂ) → ℝ} (hw : ∀ σ, w (conjugate σ) = w σ) (m : ι → ℤ) (α₀ : K) :
    sqNorm (casMatrix w b e *ᵥ (intVec m + basisCoords b α₀)) =
      weightedNormSq w (∑ j, m j • b j + α₀) := by
  unfold sqNorm weightedNormSq
  simp_rw [casMatrix_mulVec_shift]
  rw [Equiv.sum_comp e (fun σ => casCoord w (∑ j, m j • b j + α₀) σ ^ 2), sum_sq_casCoord hw]

/-- **Hecke's theta transformation for the coset `α₀ + ℤ b`.** The dual side carries the
additive phases `e(n·v)`, `v` the coordinates of `α₀`. -/
theorem tsum_traceDual_theta_shift (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ))
    {w w' : (K →+* ℂ) → ℝ} (hw : ∀ σ, w (conjugate σ) = w σ) (hww : ∀ σ, w' σ * w σ = 1)
    {t : ℝ} (ht : 0 < t) (α₀ : K) :
    ∑' m : ι → ℤ, ((Real.exp (-(π * t) * weightedNormSq w (∑ j, m j • b j + α₀)) : ℝ) : ℂ) =
      ((|(casMatrix w b e).det|⁻¹ * (1 / t) ^ ((Fintype.card ι : ℝ) / 2) : ℝ) : ℂ) *
        ∑' n : ι → ℤ, charPi n (-basisCoords b α₀) *
          ((Real.exp (-π * weightedNormSq w' (∑ j, n j • b.traceDual j) / t) : ℝ) : ℂ) := by
  have hw' := conj_inv_weight hw hww
  have h := tsum_shiftedGaussian_eq (casEquiv b e hww) ht (basisCoords b α₀)
  have hdet : LinearMap.det ((casEquiv b e hww : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) :
      (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) = (casMatrix w b e).det := by
    have : ((casEquiv b e hww : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) =
        Matrix.toLin' (casMatrix w b e) := rfl
    rw [this, LinearMap.det_toLin']
  rw [hdet] at h
  simp_rw [casEquiv_apply, dualEquiv_casEquiv_apply, sqNorm_casMatrix_mulVec_shift b e hw,
    sqNorm_casMatrix'_mulVec b.traceDual e hw'] at h
  exact h

end SimultaneousPrimitiveRoots.Hecke

end
