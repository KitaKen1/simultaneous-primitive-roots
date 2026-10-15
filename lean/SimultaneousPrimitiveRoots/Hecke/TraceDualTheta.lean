module

public import SimultaneousPrimitiveRoots.Hecke.EpsteinZeta
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.Trace.Basic

/-!
# The theta transformation for a lattice of a number field and its trace dual

Let `K` be a number field, `b` a `ℚ`-basis of `K` and `b^∨ = b.traceDual` the dual basis for the
trace form, `Tr(b^∨_i b_j) = δ_ij`. For positive weights `y_σ` on the complex embeddings,
invariant under complex conjugation, put `Q_y(x) = ∑_σ y_σ |σ x|²`. Then

`∑_{m ∈ ℤ^n} exp(-π t Q_y(∑ m_j b_j))
  = |det|⁻¹ t^{-n/2} ∑_{n ∈ ℤ^n} exp(-π Q_{1/y}(∑ n_j b^∨_j) / t)`.

The proof feeds the lattice theta transformation `tsum_gaussian_eq` (D2) with the *Hartley
coordinates* `σ ↦ √y_σ (Re σ x + Im σ x)`. Their squares sum to `Q_y`, and the conjugate
coordinates `σ ↦ (Re σ x - Im σ x)/√y_σ` pair with them to the trace form. So the dual lattice
of D2 is exactly the trace dual, and no choice of one embedding from each conjugate pair is needed.

This is step D3c of the B7 blueprint (`docs/b7-dedekind-blueprint.md`).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField NumberField.ComplexEmbedding Complex Matrix
open scoped Real ComplexConjugate

variable {K : Type*} [Field K] [NumberField K]

/-- The trace as a sum over the complex embeddings. -/
theorem trace_eq_sum_complexEmbeddings (x : K) :
    ((Algebra.trace ℚ K x : ℚ) : ℂ) = ∑ σ : K →+* ℂ, σ x := by
  have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := x)
  rw [eq_ratCast] at h
  rw [h]
  exact (Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => φ x) (fun σ => σ x)
    (fun _ => rfl)).symm

/-- Summing over the conjugate embeddings is a reindexing. -/
theorem sum_conjugate (g : (K →+* ℂ) → ℝ) : ∑ σ, g (conjugate σ) = ∑ σ, g σ := by
  have := Equiv.sum_comp (Function.Involutive.toPerm _ (involutive_conjugate K)) g
  simpa using this

/-- Weighted Hartley coordinates `σ ↦ w σ · (Re σ x + Im σ x)`. -/
def casCoord (w : (K →+* ℂ) → ℝ) (x : K) : (K →+* ℂ) → ℝ :=
  fun σ => w σ * ((σ x).re + (σ x).im)

/-- Conjugate Hartley coordinates `σ ↦ w σ · (Re σ x - Im σ x)`, used on the dual side. -/
def casCoord' (w : (K →+* ℂ) → ℝ) (x : K) : (K →+* ℂ) → ℝ :=
  fun σ => w σ * ((σ x).re - (σ x).im)

/-- The Hartley coordinates are additive in `x`. -/
theorem casCoord_sum_zsmul {ι : Type*} [Fintype ι] (w : (K →+* ℂ) → ℝ) (b : ι → K)
    (m : ι → ℤ) (σ : K →+* ℂ) :
    casCoord w (∑ j, m j • b j) σ = ∑ j, (m j : ℝ) * casCoord w (b j) σ := by
  unfold casCoord
  have hre : (σ (∑ j, m j • b j)).re = ∑ j, (m j : ℝ) * (σ (b j)).re := by
    rw [map_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_zsmul, zsmul_eq_mul, Complex.mul_re]
    simp
  have him : (σ (∑ j, m j • b j)).im = ∑ j, (m j : ℝ) * (σ (b j)).im := by
    rw [map_sum, Complex.im_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_zsmul, zsmul_eq_mul, Complex.mul_im]
    simp
  rw [hre, him, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem casCoord'_sum_zsmul {ι : Type*} [Fintype ι] (w : (K →+* ℂ) → ℝ) (b : ι → K)
    (m : ι → ℤ) (σ : K →+* ℂ) :
    casCoord' w (∑ j, m j • b j) σ = ∑ j, (m j : ℝ) * casCoord' w (b j) σ := by
  unfold casCoord'
  have hre : (σ (∑ j, m j • b j)).re = ∑ j, (m j : ℝ) * (σ (b j)).re := by
    rw [map_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_zsmul, zsmul_eq_mul, Complex.mul_re]
    simp
  have him : (σ (∑ j, m j • b j)).im = ∑ j, (m j : ℝ) * (σ (b j)).im := by
    rw [map_sum, Complex.im_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_zsmul, zsmul_eq_mul, Complex.mul_im]
    simp
  rw [hre, him, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The squared Hartley coordinates sum to the weighted quadratic form. -/
theorem sum_sq_casCoord {w : (K →+* ℂ) → ℝ} (hw : ∀ σ, w (conjugate σ) = w σ) (x : K) :
    ∑ σ, casCoord w x σ ^ 2 = ∑ σ, w σ ^ 2 * Complex.normSq (σ x) := by
  unfold casCoord
  have h1 : ∑ σ : K →+* ℂ, (w σ * ((σ x).re + (σ x).im)) ^ 2 =
      ∑ σ : K →+* ℂ, (w σ * ((σ x).re - (σ x).im)) ^ 2 := by
    rw [← sum_conjugate (fun σ => (w σ * ((σ x).re + (σ x).im)) ^ 2)]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [conjugate_coe_eq, Complex.conj_re, Complex.conj_im, hw]
    ring
  have h2 : ∑ σ : K →+* ℂ, (w σ * ((σ x).re + (σ x).im)) ^ 2 +
      ∑ σ : K →+* ℂ, (w σ * ((σ x).re - (σ x).im)) ^ 2 =
      2 * ∑ σ : K →+* ℂ, w σ ^ 2 * Complex.normSq (σ x) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [Complex.normSq_apply]
    ring
  linarith

theorem sum_sq_casCoord' {w : (K →+* ℂ) → ℝ} (hw : ∀ σ, w (conjugate σ) = w σ) (x : K) :
    ∑ σ, casCoord' w x σ ^ 2 = ∑ σ, w σ ^ 2 * Complex.normSq (σ x) := by
  unfold casCoord'
  have h1 : ∑ σ : K →+* ℂ, (w σ * ((σ x).re - (σ x).im)) ^ 2 =
      ∑ σ : K →+* ℂ, (w σ * ((σ x).re + (σ x).im)) ^ 2 := by
    rw [← sum_conjugate (fun σ => (w σ * ((σ x).re - (σ x).im)) ^ 2)]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [conjugate_coe_eq, Complex.conj_re, Complex.conj_im, hw]
    ring
  have h2 : ∑ σ : K →+* ℂ, (w σ * ((σ x).re - (σ x).im)) ^ 2 +
      ∑ σ : K →+* ℂ, (w σ * ((σ x).re + (σ x).im)) ^ 2 =
      2 * ∑ σ : K →+* ℂ, w σ ^ 2 * Complex.normSq (σ x) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [Complex.normSq_apply]
    ring
  linarith

/-- **The Hartley coordinates pair to the trace form.** -/
theorem sum_casCoord'_mul_casCoord {w w' : (K →+* ℂ) → ℝ} (hww : ∀ σ, w' σ * w σ = 1)
    (z x : K) :
    ∑ σ, casCoord' w' z σ * casCoord w x σ = (Algebra.trace ℚ K (z * x) : ℝ) := by
  unfold casCoord casCoord'
  have hsplit : ∀ σ : K →+* ℂ,
      w' σ * ((σ z).re - (σ z).im) * (w σ * ((σ x).re + (σ x).im)) =
        (σ (z * x)).re + ((σ z).re * (σ x).im - (σ z).im * (σ x).re) := by
    intro σ
    rw [map_mul, Complex.mul_re]
    calc w' σ * ((σ z).re - (σ z).im) * (w σ * ((σ x).re + (σ x).im))
        = (w' σ * w σ) * (((σ z).re - (σ z).im) * ((σ x).re + (σ x).im)) := by ring
      _ = _ := by rw [hww σ]; ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  have hcross : ∑ σ : K →+* ℂ, ((σ z).re * (σ x).im - (σ z).im * (σ x).re) = 0 := by
    have h := sum_conjugate (K := K) (fun σ => (σ z).re * (σ x).im - (σ z).im * (σ x).re)
    simp only [conjugate_coe_eq, Complex.conj_re, Complex.conj_im] at h
    have h' : ∑ σ : K →+* ℂ, ((σ z).re * -(σ x).im - -(σ z).im * (σ x).re) =
        -∑ σ : K →+* ℂ, ((σ z).re * (σ x).im - (σ z).im * (σ x).re) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro σ _
      ring
    linarith
  rw [hcross, add_zero]
  have htr := congrArg Complex.re (trace_eq_sum_complexEmbeddings (z * x))
  rw [Complex.re_sum] at htr
  rw [← htr, Complex.ratCast_re]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix of Hartley coordinates of the family `b`, rows indexed through `e`. -/
def casMatrix (w : (K →+* ℂ) → ℝ) (b : ι → K) (e : ι ≃ (K →+* ℂ)) : Matrix ι ι ℝ :=
  fun i j => casCoord w (b j) (e i)

/-- The matrix of conjugate Hartley coordinates. -/
def casMatrix' (w : (K →+* ℂ) → ℝ) (b : ι → K) (e : ι ≃ (K →+* ℂ)) : Matrix ι ι ℝ :=
  fun i j => casCoord' w (b j) (e i)

/-- The trace-dual basis gives the transpose inverse of the Hartley matrix. -/
theorem casMatrix'_transpose_mul (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ))
    {w w' : (K →+* ℂ) → ℝ} (hww : ∀ σ, w' σ * w σ = 1) :
    (casMatrix' w' b.traceDual e)ᵀ * casMatrix w b e = 1 := by
  refine Matrix.ext fun j k => ?_
  rw [Matrix.mul_apply, Matrix.one_apply]
  have h := Equiv.sum_comp e (fun σ => casCoord' w' (b.traceDual j) σ * casCoord w (b k) σ)
  have hsum : ∑ x, (casMatrix' w' b.traceDual e)ᵀ j x * casMatrix w b e x k =
      ∑ x, casCoord' w' (b.traceDual j) (e x) * casCoord w (b k) (e x) := rfl
  rw [hsum, h, sum_casCoord'_mul_casCoord hww, Module.Basis.trace_traceDual_mul]
  by_cases hjk : j = k
  · subst hjk
    simp
  · have hkj : k ≠ j := fun h => hjk h.symm
    simp [hjk, hkj]

theorem casMatrix_mul_transpose (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ))
    {w w' : (K →+* ℂ) → ℝ} (hww : ∀ σ, w' σ * w σ = 1) :
    casMatrix w b e * (casMatrix' w' b.traceDual e)ᵀ = 1 :=
  mul_eq_one_comm.mp (casMatrix'_transpose_mul b e hww)

/-- The Hartley coordinate map of the basis `b`, as a linear automorphism of `ℝ^ι`. -/
def casEquiv (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ)) {w w' : (K →+* ℂ) → ℝ}
    (hww : ∀ σ, w' σ * w σ = 1) : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (casMatrix w b e))
    (Matrix.toLin' (casMatrix' w' b.traceDual e)ᵀ)
    (by rw [← Matrix.toLin'_mul, casMatrix_mul_transpose b e hww, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, casMatrix'_transpose_mul b e hww, Matrix.toLin'_one])

theorem casEquiv_apply (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ)) {w w' : (K →+* ℂ) → ℝ}
    (hww : ∀ σ, w' σ * w σ = 1) (v : ι → ℝ) :
    casEquiv b e hww v = casMatrix w b e *ᵥ v := by
  simp [casEquiv, Matrix.toLin'_apply]

theorem invMatrix_casEquiv (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ))
    {w w' : (K →+* ℂ) → ℝ} (hww : ∀ σ, w' σ * w σ = 1) :
    invMatrix (casEquiv b e hww) = (casMatrix' w' b.traceDual e)ᵀ := by
  unfold invMatrix
  have : ((casEquiv b e hww).symm : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) =
      Matrix.toLin' (casMatrix' w' b.traceDual e)ᵀ := rfl
  rw [this, LinearMap.toMatrix'_toLin']

/-- **The dual lattice of D2 is the trace dual.** -/
theorem dualEquiv_casEquiv_apply (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ))
    {w w' : (K →+* ℂ) → ℝ} (hww : ∀ σ, w' σ * w σ = 1) (v : ι → ℝ) :
    dualEquiv (casEquiv b e hww) v = casMatrix' w' b.traceDual e *ᵥ v := by
  rw [dualEquiv_apply, invMatrix_casEquiv, Matrix.transpose_transpose]

omit [DecidableEq ι] in
/-- The coordinates of a lattice vector. -/
theorem casMatrix_mulVec_intVec (w : (K →+* ℂ) → ℝ) (b : ι → K) (e : ι ≃ (K →+* ℂ))
    (m : ι → ℤ) (i : ι) :
    (casMatrix w b e *ᵥ intVec m) i = casCoord w (∑ j, m j • b j) (e i) := by
  rw [casCoord_sum_zsmul]
  simp only [Matrix.mulVec, dotProduct, casMatrix, intVec]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq ι] in
theorem casMatrix'_mulVec_intVec (w : (K →+* ℂ) → ℝ) (b : ι → K) (e : ι ≃ (K →+* ℂ))
    (m : ι → ℤ) (i : ι) :
    (casMatrix' w b e *ᵥ intVec m) i = casCoord' w (∑ j, m j • b j) (e i) := by
  rw [casCoord'_sum_zsmul]
  simp only [Matrix.mulVec, dotProduct, casMatrix', intVec]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sqNorm_casMatrix_mulVec (b : ι → K) (e : ι ≃ (K →+* ℂ)) {w : (K →+* ℂ) → ℝ}
    (hw : ∀ σ, w (conjugate σ) = w σ) (m : ι → ℤ) :
    sqNorm (casMatrix w b e *ᵥ intVec m) =
      ∑ σ, w σ ^ 2 * Complex.normSq (σ (∑ j, m j • b j)) := by
  unfold sqNorm
  simp_rw [casMatrix_mulVec_intVec]
  rw [Equiv.sum_comp e (fun σ => casCoord w (∑ j, m j • b j) σ ^ 2), sum_sq_casCoord hw]

theorem sqNorm_casMatrix'_mulVec (b : ι → K) (e : ι ≃ (K →+* ℂ)) {w : (K →+* ℂ) → ℝ}
    (hw : ∀ σ, w (conjugate σ) = w σ) (m : ι → ℤ) :
    sqNorm (casMatrix' w b e *ᵥ intVec m) =
      ∑ σ, w σ ^ 2 * Complex.normSq (σ (∑ j, m j • b j)) := by
  unfold sqNorm
  simp_rw [casMatrix'_mulVec_intVec]
  rw [Equiv.sum_comp e (fun σ => casCoord' w (∑ j, m j • b j) σ ^ 2), sum_sq_casCoord' hw]

/-- The weighted norm form `Q_w(x) = ∑_σ w_σ² |σ x|²`. -/
def weightedNormSq (w : (K →+* ℂ) → ℝ) (x : K) : ℝ := ∑ σ, w σ ^ 2 * Complex.normSq (σ x)

omit [NumberField K] in
theorem conj_inv_weight {w w' : (K →+* ℂ) → ℝ} (hw : ∀ σ, w (conjugate σ) = w σ)
    (hww : ∀ σ, w' σ * w σ = 1) : ∀ σ, w' (conjugate σ) = w' σ := by
  intro σ
  have h1 := hww σ
  have h2 := hww (conjugate σ)
  rw [hw] at h2
  have hw0 : w σ ≠ 0 := by
    intro h
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  exact mul_right_cancel₀ hw0 (h2.trans h1.symm)

/-- **Hecke's theta transformation for a basis of `K` and its trace dual.** -/
theorem tsum_traceDual_theta (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ))
    {w w' : (K →+* ℂ) → ℝ} (hw : ∀ σ, w (conjugate σ) = w σ) (hww : ∀ σ, w' σ * w σ = 1)
    {t : ℝ} (ht : 0 < t) :
    ∑' m : ι → ℤ, Real.exp (-(π * t) * weightedNormSq w (∑ j, m j • b j)) =
      |(casMatrix w b e).det|⁻¹ * (1 / t) ^ ((Fintype.card ι : ℝ) / 2) *
        ∑' n : ι → ℤ, Real.exp (-π * weightedNormSq w' (∑ j, n j • b.traceDual j) / t) := by
  have hw' := conj_inv_weight hw hww
  have h := tsum_gaussian_eq (casEquiv b e hww) ht
  have hdet : LinearMap.det ((casEquiv b e hww : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) :
      (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) = (casMatrix w b e).det := by
    have : ((casEquiv b e hww : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) =
        Matrix.toLin' (casMatrix w b e) := rfl
    rw [this, LinearMap.det_toLin']
  rw [hdet] at h
  simp_rw [casEquiv_apply, dualEquiv_casEquiv_apply, sqNorm_casMatrix_mulVec b e hw,
    sqNorm_casMatrix'_mulVec b.traceDual e hw'] at h
  exact h

end SimultaneousPrimitiveRoots.Hecke

end
