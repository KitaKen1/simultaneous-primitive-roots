module

public import SimultaneousPrimitiveRoots.Hecke.NumberFieldTheta
public import Mathlib.RingTheory.Discriminant

/-!
# The covolume of a Hartley lattice is `√|disc|`

For a `ℚ`-basis `b` of `K`, the unweighted Hartley matrix `C` (`casMatrix 1 b e`) satisfies
`det(C)² = |disc(b)|`. Indeed `Cᵀ C = Mᵀ conj(M)` with `M_{σ j} = σ(b_j)`, because the imaginary
parts cancel in conjugate pairs, so `det(C)² = |det M|² = |disc b|`
(`Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two`).

This gives the covolume `√|d_K| · N(J)` of the lattice of an ideal `J`, the constant in Hecke's
functional equation.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField NumberField.ComplexEmbedding Complex Matrix
open scoped ComplexConjugate

variable {K : Type*} [Field K] [NumberField K]

/-- The bilinear Hartley pairing. -/
theorem sum_casCoord_mul_casCoord (x y : K) :
    ∑ σ : K →+* ℂ, casCoord (fun _ => 1) x σ * casCoord (fun _ => 1) y σ =
      ∑ σ : K →+* ℂ, ((σ x).re * (σ y).re + (σ x).im * (σ y).im) := by
  unfold casCoord
  have h1 : ∑ σ : K →+* ℂ, (1 * ((σ x).re + (σ x).im)) * (1 * ((σ y).re + (σ y).im)) =
      ∑ σ : K →+* ℂ, (((σ x).re - (σ x).im) * ((σ y).re - (σ y).im)) := by
    rw [← sum_conjugate (fun σ => (1 * ((σ x).re + (σ x).im)) * (1 * ((σ y).re + (σ y).im)))]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [conjugate_coe_eq, Complex.conj_re, Complex.conj_im]
    ring
  have h2 : ∑ σ : K →+* ℂ, (1 * ((σ x).re + (σ x).im)) * (1 * ((σ y).re + (σ y).im)) +
      ∑ σ : K →+* ℂ, (((σ x).re - (σ x).im) * ((σ y).re - (σ y).im)) =
      2 * ∑ σ : K →+* ℂ, ((σ x).re * (σ y).re + (σ x).im * (σ y).im) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  linarith

/-- `∑_σ σ(x) conj(σ(y))` is real. -/
theorem sum_mul_conj_eq_ofReal (x y : K) :
    ∑ σ : K →+* ℂ, σ x * conj (σ y) =
      ((∑ σ : K →+* ℂ, ((σ x).re * (σ y).re + (σ x).im * (σ y).im) : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.re_sum, Complex.ofReal_re]
    apply Finset.sum_congr rfl
    intro σ _
    simp [Complex.mul_re]
  · rw [Complex.im_sum, Complex.ofReal_im]
    have h := sum_conjugate (K := K) (fun σ => (σ x * conj (σ y)).im)
    simp only [conjugate_coe_eq] at h
    have h' : ∑ σ : K →+* ℂ, (conj (σ x) * conj (conj (σ y))).im =
        -∑ σ : K →+* ℂ, (σ x * conj (σ y)).im := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro σ _
      simp [Complex.mul_im]
      ring
    linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complex embedding matrix `M_{i j} = (e i)(b j)`. -/
def embMatrix (b : ι → K) (e : ι ≃ (K →+* ℂ)) : Matrix ι ι ℂ := fun i j => (e i) (b j)

/-- The Gram matrix of the Hartley coordinates. -/
def casGram (b : ι → K) : Matrix ι ι ℝ :=
  fun j k => ∑ σ : K →+* ℂ, ((σ (b j)).re * (σ (b k)).re + (σ (b j)).im * (σ (b k)).im)

omit [DecidableEq ι] in
theorem casMatrix_transpose_mul (b : ι → K) (e : ι ≃ (K →+* ℂ)) :
    (casMatrix (fun _ => 1) b e)ᵀ * casMatrix (fun _ => 1) b e = casGram b := by
  refine Matrix.ext fun j k => ?_
  rw [Matrix.mul_apply]
  have hsum : ∑ i, (casMatrix (fun _ => 1) b e)ᵀ j i * casMatrix (fun _ => 1) b e i k =
      ∑ i, casCoord (fun _ => 1) (b j) (e i) * casCoord (fun _ => 1) (b k) (e i) := rfl
  rw [hsum, Equiv.sum_comp e (fun σ => casCoord (fun _ => 1) (b j) σ *
    casCoord (fun _ => 1) (b k) σ), sum_casCoord_mul_casCoord]
  rfl

omit [DecidableEq ι] in
theorem embMatrix_transpose_mul_conj (b : ι → K) (e : ι ≃ (K →+* ℂ)) :
    (embMatrix b e)ᵀ * (embMatrix b e).map (starRingEnd ℂ) =
      (casGram b).map (Complex.ofRealHom : ℝ →+* ℂ) := by
  refine Matrix.ext fun j k => ?_
  rw [Matrix.mul_apply]
  have hsum : ∑ i, (embMatrix b e)ᵀ j i * (embMatrix b e).map (starRingEnd ℂ) i k =
      ∑ i, (e i) (b j) * conj ((e i) (b k)) := rfl
  rw [hsum, Equiv.sum_comp e (fun σ => σ (b j) * conj (σ (b k))), sum_mul_conj_eq_ofReal]
  rfl

/-- `det(C)² = |det M|²`. -/
theorem det_casMatrix_sq (b : ι → K) (e : ι ≃ (K →+* ℂ)) :
    (casMatrix (fun _ => 1) b e).det ^ 2 = Complex.normSq (embMatrix b e).det := by
  have h1 : (casMatrix (fun _ => 1) b e).det ^ 2 = (casGram b).det := by
    rw [← casMatrix_transpose_mul, Matrix.det_mul, Matrix.det_transpose, sq]
  have h2 : (((casGram b).det : ℝ) : ℂ) = ((Complex.normSq (embMatrix b e).det : ℝ) : ℂ) := by
    have hc := congrArg Matrix.det (embMatrix_transpose_mul_conj b e)
    have e1 : ((embMatrix b e).map (starRingEnd ℂ)).det = conj (embMatrix b e).det :=
      (RingHom.map_det _ _).symm
    have e2 : ((casGram b).map (Complex.ofRealHom : ℝ →+* ℂ)).det =
        Complex.ofRealHom (casGram b).det := (RingHom.map_det _ _).symm
    rw [Matrix.det_mul, Matrix.det_transpose, e1, e2, Complex.mul_conj] at hc
    exact hc.symm
  rw [h1]
  exact_mod_cast h2

/-- **`det(C)² = |disc(b)|`.** -/
theorem det_casMatrix_sq_eq_abs_discr (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ)) :
    (casMatrix (fun _ => 1) (b : ι → K) e).det ^ 2 = |((Algebra.discr ℚ (b : ι → K) : ℚ) : ℝ)| := by
  rw [det_casMatrix_sq]
  let e' : ι ≃ (K →ₐ[ℚ] ℂ) := e.trans (RingHom.equivRatAlgHom K ℂ)
  have hd := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (b : ι → K) e'
  have hM : embMatrix (b : ι → K) e = (Algebra.embeddingsMatrixReindex ℚ ℂ (b : ι → K) e')ᵀ := by
    refine Matrix.ext fun i j => ?_
    rfl
  rw [hM, Matrix.det_transpose, Complex.normSq_eq_norm_sq, ← norm_pow, ← hd, eq_ratCast,
    ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

end SimultaneousPrimitiveRoots.Hecke

end
