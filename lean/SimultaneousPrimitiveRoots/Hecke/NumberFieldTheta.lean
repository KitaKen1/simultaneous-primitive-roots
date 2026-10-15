module

public import SimultaneousPrimitiveRoots.Hecke.TraceDualTheta
public import SimultaneousPrimitiveRoots.Hecke.AveragedMellin

/-!
# Hecke theta families of a number field

A *weight family* is a continuous family `p ↦ y_p` of positive weights on the complex embeddings of
`K`, invariant under complex conjugation, uniformly bounded above and below, with
`∏_σ y_p(σ) = 1`. For a `ℚ`-basis `b` of `K` (for instance a `ℤ`-basis of a fractional ideal), the
Hartley coordinates with weights `√y_p` give a `ThetaFamily`: the lattices have constant covolume
`|det casMatrix 1|`, and their duals are the trace-dual lattices with weights `1/√y_p`.

So the averaged theta functions of `b` and `b.traceDual` form a weak FE-pair
(`ThetaFamily.fePair`) whose Mellin transform is the averaged Epstein zeta function of the norm
forms `Q_{y_p}(x) = ∑_σ y_p(σ) |σ x|²` (step D3, number-field form).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField NumberField.ComplexEmbedding Complex Matrix MeasureTheory Set
open scoped Real

variable {K : Type*} [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField K] in
theorem casCoord_eq_mul (w : (K →+* ℂ) → ℝ) (x : K) (σ : K →+* ℂ) :
    casCoord w x σ = w σ * casCoord (fun _ => 1) x σ := by
  simp [casCoord]

omit [NumberField K] in
theorem casCoord'_eq_mul (w : (K →+* ℂ) → ℝ) (x : K) (σ : K →+* ℂ) :
    casCoord' w x σ = w σ * casCoord' (fun _ => 1) x σ := by
  simp [casCoord']

omit [NumberField K] [DecidableEq ι] in
theorem casMatrix_mulVec_eq (w : (K →+* ℂ) → ℝ) (b : ι → K) (e : ι ≃ (K →+* ℂ))
    (v : ι → ℝ) (i : ι) :
    (casMatrix w b e *ᵥ v) i = w (e i) * (casMatrix (fun _ => 1) b e *ᵥ v) i := by
  simp only [Matrix.mulVec, dotProduct, casMatrix]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [casCoord_eq_mul]
  ring

omit [NumberField K] [DecidableEq ι] in
theorem casMatrix'_mulVec_eq (w : (K →+* ℂ) → ℝ) (b : ι → K) (e : ι ≃ (K →+* ℂ))
    (v : ι → ℝ) (i : ι) :
    (casMatrix' w b e *ᵥ v) i = w (e i) * (casMatrix' (fun _ => 1) b e *ᵥ v) i := by
  simp only [Matrix.mulVec, dotProduct, casMatrix']
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [casCoord'_eq_mul]
  ring

omit [NumberField K] in
theorem casMatrix_eq_diagonal_mul (w : (K →+* ℂ) → ℝ) (b : ι → K) (e : ι ≃ (K →+* ℂ)) :
    casMatrix w b e = Matrix.diagonal (fun i => w (e i)) * casMatrix (fun _ => 1) b e := by
  ext i j
  rw [Matrix.diagonal_mul]
  exact casCoord_eq_mul w (b j) (e i)

theorem det_casMatrix (w : (K →+* ℂ) → ℝ) (b : ι → K) (e : ι ≃ (K →+* ℂ)) :
    (casMatrix w b e).det = (∏ σ, w σ) * (casMatrix (fun _ => 1) b e).det := by
  rw [casMatrix_eq_diagonal_mul, Matrix.det_mul, Matrix.det_diagonal]
  congr 1
  exact Equiv.prod_comp e w

theorem det_casEquiv (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ)) {w w' : (K →+* ℂ) → ℝ}
    (hww : ∀ σ, w' σ * w σ = 1) :
    LinearMap.det ((casEquiv b e hww : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) =
      (casMatrix w b e).det := by
  have : ((casEquiv b e hww : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) =
      Matrix.toLin' (casMatrix w b e) := rfl
  rw [this, LinearMap.det_toLin']

/-- The unweighted Hartley map of a basis. -/
def casEquiv₁ (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ)) : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  casEquiv b e (w := fun _ => 1) (w' := fun _ => 1) (fun _ => one_mul 1)

/-- A chosen ellipticity constant of an invertible linear map. -/
def ellip {d : Type*} [Fintype d] (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) : ℝ :=
  Classical.choose (exists_sqNorm_lower A)

theorem ellip_pos {d : Type*} [Fintype d] (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) : 0 < ellip A :=
  (Classical.choose_spec (exists_sqNorm_lower A)).1

theorem ellip_le {d : Type*} [Fintype d] (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (v : d → ℝ) :
    ellip A * ‖v‖ ^ 2 ≤ sqNorm (A v) :=
  (Classical.choose_spec (exists_sqNorm_lower A)).2 v

/-- A continuous, conjugation-invariant, uniformly bounded family of norm-one weights. -/
structure WeightFamily (K P : Type*) [Field K] [NumberField K] [TopologicalSpace P] where
  /-- The weights `y_p(σ)`. -/
  y : P → (K →+* ℂ) → ℝ
  continuous_y : ∀ σ, Continuous fun p => y p σ
  conj : ∀ p σ, y p (conjugate σ) = y p σ
  /-- A uniform logarithmic bound for the weights. -/
  L : ℝ
  lower : ∀ p σ, Real.exp (-L) ≤ y p σ
  upper : ∀ p σ, y p σ ≤ Real.exp L
  prod_eq_one : ∀ p, ∏ σ, y p σ = 1

namespace WeightFamily

variable {P : Type*} [TopologicalSpace P] (W : WeightFamily K P)

theorem y_pos (p : P) (σ : K →+* ℂ) : 0 < W.y p σ :=
  lt_of_lt_of_le (Real.exp_pos _) (W.lower p σ)

/-- The square-root weights `√y_p`. -/
def w (p : P) (σ : K →+* ℂ) : ℝ := Real.sqrt (W.y p σ)

/-- The inverse square-root weights `1/√y_p`. -/
def w' (p : P) (σ : K →+* ℂ) : ℝ := 1 / Real.sqrt (W.y p σ)

theorem w_pos (p : P) (σ : K →+* ℂ) : 0 < W.w p σ := Real.sqrt_pos.mpr (W.y_pos p σ)

theorem hww (p : P) : ∀ σ, W.w' p σ * W.w p σ = 1 := fun σ =>
  one_div_mul_cancel (W.w_pos p σ).ne'

theorem w_conj (p : P) : ∀ σ, W.w p (conjugate σ) = W.w p σ := fun σ => by
  simp only [w, W.conj]

theorem w_sq (p : P) (σ : K →+* ℂ) : W.w p σ ^ 2 = W.y p σ :=
  Real.sq_sqrt (W.y_pos p σ).le

theorem w'_sq (p : P) (σ : K →+* ℂ) : W.w' p σ ^ 2 = (W.y p σ)⁻¹ := by
  rw [w', div_pow, Real.sq_sqrt (W.y_pos p σ).le, one_pow, one_div]

theorem prod_w (p : P) : ∏ σ, W.w p σ = 1 := by
  have h0 : 0 ≤ ∏ σ, W.w p σ := Finset.prod_nonneg fun σ _ => (W.w_pos p σ).le
  have h1 : (∏ σ, W.w p σ) * (∏ σ, W.w p σ) = 1 := by
    rw [← Finset.prod_mul_distrib]
    have : ∀ σ, W.w p σ * W.w p σ = W.y p σ := fun σ => by rw [← sq, W.w_sq]
    simp_rw [this]
    exact W.prod_eq_one p
  rcases mul_self_eq_one_iff.mp h1 with h | h
  · exact h
  · linarith

theorem continuous_w (σ : K →+* ℂ) : Continuous fun p => W.w p σ :=
  Real.continuous_sqrt.comp (W.continuous_y σ)

theorem continuous_w' (σ : K →+* ℂ) : Continuous fun p => W.w' p σ :=
  continuous_const.div (W.continuous_w σ) fun p => (W.w_pos p σ).ne'

variable (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ))

theorem sqNorm_casMatrix_ge (p : P) (v : ι → ℝ) :
    Real.exp (-W.L) * sqNorm (casEquiv₁ b e v) ≤ sqNorm (casEquiv b e (W.hww p) v) := by
  unfold sqNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h1 : casEquiv b e (W.hww p) v i = W.w p (e i) * casEquiv₁ b e v i := by
    rw [casEquiv_apply, casEquiv₁, casEquiv_apply, casMatrix_mulVec_eq]
  rw [h1, mul_pow, W.w_sq]
  exact mul_le_mul_of_nonneg_right (W.lower p (e i)) (sq_nonneg _)

theorem sqNorm_casMatrix'_ge (p : P) (v : ι → ℝ) :
    Real.exp (-W.L) * sqNorm (dualEquiv (casEquiv₁ b e) v) ≤
      sqNorm (dualEquiv (casEquiv b e (W.hww p)) v) := by
  unfold sqNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h1 : dualEquiv (casEquiv b e (W.hww p)) v i =
      W.w' p (e i) * dualEquiv (casEquiv₁ b e) v i := by
    rw [dualEquiv_casEquiv_apply, casEquiv₁, dualEquiv_casEquiv_apply, casMatrix'_mulVec_eq]
  rw [h1, mul_pow, W.w'_sq]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hy := W.upper p (e i)
  have hy0 := W.y_pos p (e i)
  rw [Real.exp_neg]
  exact inv_anti₀ hy0 hy

/-- **The Hecke theta family of a basis of `K` and a weight family.** -/
def thetaFamily : ThetaFamily ι P where
  A p := casEquiv b e (W.hww p)
  continuous_A v := by
    refine continuous_pi fun i => ?_
    have h : ∀ p, casEquiv b e (W.hww p) v i = W.w p (e i) * casEquiv₁ b e v i := fun p => by
      rw [casEquiv_apply, casEquiv₁, casEquiv_apply, casMatrix_mulVec_eq]
    simp_rw [h]
    exact (W.continuous_w (e i)).mul continuous_const
  continuous_dual v := by
    refine continuous_pi fun i => ?_
    have h : ∀ p, dualEquiv (casEquiv b e (W.hww p)) v i =
        W.w' p (e i) * dualEquiv (casEquiv₁ b e) v i := fun p => by
      rw [dualEquiv_casEquiv_apply, casEquiv₁, dualEquiv_casEquiv_apply, casMatrix'_mulVec_eq]
    simp_rw [h]
    exact (W.continuous_w' (e i)).mul continuous_const
  κ := Real.exp (-W.L) * min (ellip (casEquiv₁ b e)) (ellip (dualEquiv (casEquiv₁ b e)))
  κ_pos := mul_pos (Real.exp_pos _) (lt_min (ellip_pos _) (ellip_pos _))
  lower p v := by
    have h1 := W.sqNorm_casMatrix_ge b e p v
    have h2 := ellip_le (casEquiv₁ b e) v
    have h3 : min (ellip (casEquiv₁ b e)) (ellip (dualEquiv (casEquiv₁ b e))) * ‖v‖ ^ 2 ≤
        ellip (casEquiv₁ b e) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
    have h4 := mul_le_mul_of_nonneg_left (h3.trans h2) (Real.exp_pos (-W.L)).le
    calc Real.exp (-W.L) * min (ellip (casEquiv₁ b e)) (ellip (dualEquiv (casEquiv₁ b e))) *
          ‖v‖ ^ 2
        = Real.exp (-W.L) * (min (ellip (casEquiv₁ b e)) (ellip (dualEquiv (casEquiv₁ b e))) *
          ‖v‖ ^ 2) := by ring
      _ ≤ Real.exp (-W.L) * sqNorm (casEquiv₁ b e v) := h4
      _ ≤ _ := h1
  lower_dual p v := by
    have h1 := W.sqNorm_casMatrix'_ge b e p v
    have h2 := ellip_le (dualEquiv (casEquiv₁ b e)) v
    have h3 : min (ellip (casEquiv₁ b e)) (ellip (dualEquiv (casEquiv₁ b e))) * ‖v‖ ^ 2 ≤
        ellip (dualEquiv (casEquiv₁ b e)) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
    have h4 := mul_le_mul_of_nonneg_left (h3.trans h2) (Real.exp_pos (-W.L)).le
    calc Real.exp (-W.L) * min (ellip (casEquiv₁ b e)) (ellip (dualEquiv (casEquiv₁ b e))) *
          ‖v‖ ^ 2
        = Real.exp (-W.L) * (min (ellip (casEquiv₁ b e)) (ellip (dualEquiv (casEquiv₁ b e))) *
          ‖v‖ ^ 2) := by ring
      _ ≤ Real.exp (-W.L) * sqNorm (dualEquiv (casEquiv₁ b e) v) := h4
      _ ≤ _ := h1
  covol := |(casMatrix (fun _ => 1) b e).det|
  covol_pos := by
    have h := det_ne_zero (casEquiv₁ b e)
    rw [casEquiv₁, det_casEquiv] at h
    exact abs_pos.mpr h
  abs_det p := by
    rw [det_casEquiv, det_casMatrix, W.prod_w, one_mul]

theorem thetaFamily_A (p : P) : (W.thetaFamily b e).A p = casEquiv b e (W.hww p) := rfl

/-- The lattice side of the family is the weighted norm form of `b`. -/
theorem sqNorm_thetaFamily (p : P) (m : ι → ℤ) :
    sqNorm ((W.thetaFamily b e).A p (intVec m)) = weightedNormSq (W.w p) (∑ j, m j • b j) := by
  rw [thetaFamily_A, casEquiv_apply]
  exact sqNorm_casMatrix_mulVec b e (W.w_conj p) m

/-- The dual side of the family is the weighted norm form of the trace-dual basis. -/
theorem sqNorm_thetaFamily_dual (p : P) (m : ι → ℤ) :
    sqNorm (dualEquiv ((W.thetaFamily b e).A p) (intVec m)) =
      weightedNormSq (W.w' p) (∑ j, m j • b.traceDual j) := by
  rw [thetaFamily_A, dualEquiv_casEquiv_apply]
  exact sqNorm_casMatrix'_mulVec b.traceDual e (conj_inv_weight (W.w_conj p) (W.hww p)) m

theorem weightedNormSq_w (p : P) (x : K) :
    weightedNormSq (W.w p) x = ∑ σ, W.y p σ * Complex.normSq (σ x) := by
  unfold weightedNormSq
  simp_rw [W.w_sq]

theorem weightedNormSq_w' (p : P) (x : K) :
    weightedNormSq (W.w' p) x = ∑ σ, (W.y p σ)⁻¹ * Complex.normSq (σ x) := by
  unfold weightedNormSq
  simp_rw [W.w'_sq]

end WeightFamily

end SimultaneousPrimitiveRoots.Hecke

end
