module

public import SimultaneousPrimitiveRoots.Hecke.NumberFieldTheta
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Weights from the fundamental units, and the Hecke FE-pair of a number field

Let `η_1, …, η_r` be the fundamental units of `K` (`NumberField.Units.fundSystem`). For
`p ∈ ℝ^r` put

`y_p(σ) = exp (2 ∑_i clamp(p_i) log |σ η_i|)`,   `clamp t = max 0 (min t 1)`.

On the unit cube `[0,1)^r` these are the weights `∏_i |σ η_i|^{2 p_i}`: a fundamental domain of the
unit group acting on the torus of norm-one weights. The clamp keeps the family uniformly bounded on
all of `ℝ^r`; it does not change anything on the cube, where the measure lives.

With `μ` the Lebesgue measure on the cube, `heckeFEPair K b e` is the weak FE-pair of averaged theta
functions of the lattice spanned by `b` and of its trace dual. Its `Λ` is meromorphic with poles at
most at `0` and `n/2`, satisfies `Λ(n/2 - s) = covol⁻¹ Λ^∨(s)`, and for `re s > n/2` equals

`∫_{[0,1)^r} π^{-s} Γ(s) ∑_{m ≠ 0} Q_{y_p}(∑ m_j b_j)^{-s} dp`.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField NumberField.Units NumberField.ComplexEmbedding Complex MeasureTheory Set
open scoped Real

variable (K : Type*) [Field K] [NumberField K]

variable {K} in
/-- The norm is the product of the absolute values over all complex embeddings. -/
theorem prod_norm_complexEmbeddings (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have h := congrArg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
  simp only [eq_ratCast, norm_prod] at h
  have h2 : ‖((Algebra.norm ℚ x : ℚ) : ℂ)‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [h2] at h
  rw [h]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => ‖φ x‖) (fun σ => ‖σ x‖)
    (fun _ => rfl)

/-- `log |σ η_i|` for the fundamental units. -/
def unitLog (i : Fin (rank K)) (σ : K →+* ℂ) : ℝ :=
  Real.log ‖σ ((fundSystem K i : (𝓞 K)ˣ) : K)‖

theorem sum_unitLog (i : Fin (rank K)) : ∑ σ : K →+* ℂ, unitLog K i σ = 0 := by
  unfold unitLog
  have hne : ∀ σ : K →+* ℂ, ‖σ ((fundSystem K i : (𝓞 K)ˣ) : K)‖ ≠ 0 := fun σ => by
    rw [norm_ne_zero_iff, map_ne_zero]
    exact Units.coe_ne_zero _
  rw [← Real.log_prod (fun σ _ => hne σ), prod_norm_complexEmbeddings]
  have := NumberField.Units.norm K (fundSystem K i)
  rw [show ((Algebra.norm ℚ ((fundSystem K i : (𝓞 K)ˣ) : K) : ℚ) : ℝ) =
      (((Algebra.norm ℚ ((fundSystem K i : (𝓞 K)ˣ) : K) : ℚ)) : ℝ) from rfl]
  have h1 : |((Algebra.norm ℚ ((fundSystem K i : (𝓞 K)ˣ) : K) : ℚ) : ℝ)| = 1 := by
    rw [← Rat.cast_abs, this, Rat.cast_one]
  rw [h1, Real.log_one]

theorem unitLog_conj (i : Fin (rank K)) (σ : K →+* ℂ) :
    unitLog K i (conjugate σ) = unitLog K i σ := by
  simp [unitLog, conjugate_coe_eq]

/-- The clamp `t ↦ max 0 (min t 1)`. -/
def clamp01 (t : ℝ) : ℝ := max 0 (min t 1)

theorem clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_max_left _ _

theorem clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 :=
  max_le zero_le_one (min_le_right _ _)

theorem clamp01_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clamp01 t = t := by
  unfold clamp01
  rw [min_eq_left ht.2, max_eq_right ht.1]

theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The exponent `2 ∑_i clamp(p_i) log |σ η_i|`. -/
def unitExponent (p : Fin (rank K) → ℝ) (σ : K →+* ℂ) : ℝ :=
  2 * ∑ i, clamp01 (p i) * unitLog K i σ

/-- The logarithmic bound `2 ∑_i ∑_σ |log |σ η_i||`. -/
def unitL : ℝ := 2 * ∑ i, ∑ σ : K →+* ℂ, |unitLog K i σ|

theorem abs_unitExponent_le (p : Fin (rank K) → ℝ) (σ : K →+* ℂ) :
    |unitExponent K p σ| ≤ unitL K := by
  unfold unitExponent unitL
  rw [abs_mul, abs_two]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (clamp01_nonneg _)]
  calc clamp01 (p i) * |unitLog K i σ| ≤ 1 * |unitLog K i σ| :=
        mul_le_mul_of_nonneg_right (clamp01_le_one _) (abs_nonneg _)
    _ = |unitLog K i σ| := one_mul _
    _ ≤ ∑ τ : K →+* ℂ, |unitLog K i τ| :=
        Finset.single_le_sum (f := fun τ => |unitLog K i τ|) (fun τ _ => abs_nonneg _)
          (Finset.mem_univ σ)

/-- **The weight family of the fundamental units.** -/
def unitWeights : WeightFamily K (Fin (rank K) → ℝ) where
  y p σ := Real.exp (unitExponent K p σ)
  continuous_y σ := by
    unfold unitExponent
    refine Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun i _ => ?_))
    exact (continuous_clamp01.comp (continuous_apply i)).mul continuous_const
  conj p σ := by
    simp only [unitExponent, unitLog_conj]
  L := unitL K
  lower p σ := Real.exp_le_exp.mpr (by
    have := abs_unitExponent_le K p σ
    linarith [neg_abs_le (unitExponent K p σ)])
  upper p σ := Real.exp_le_exp.mpr (by
    have := abs_unitExponent_le K p σ
    linarith [le_abs_self (unitExponent K p σ)])
  prod_eq_one p := by
    rw [← Real.exp_sum]
    unfold unitExponent
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_unitLog, mul_zero, Finset.sum_const_zero, mul_zero,
      Real.exp_zero]

/-- The unit cube `[0,1)^r`. -/
def unitCube : Set (Fin (rank K) → ℝ) := Set.pi univ fun _ => Ico (0 : ℝ) 1

/-- Lebesgue measure on the unit cube. -/
def heckeMeasure : Measure (Fin (rank K) → ℝ) := volume.restrict (unitCube K)

theorem volume_unitCube : volume (unitCube K) = 1 := by
  unfold unitCube
  rw [Real.volume_pi_Ico]
  simp

instance : IsFiniteMeasure (heckeMeasure K) := by
  unfold heckeMeasure
  rw [isFiniteMeasure_restrict, volume_unitCube]
  exact ENNReal.one_ne_top

theorem heckeMeasure_real_univ : (heckeMeasure K).real univ = 1 := by
  rw [Measure.real, heckeMeasure, Measure.restrict_apply_univ, volume_unitCube,
    ENNReal.toReal_one]

variable {K}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Hecke theta family of the lattice spanned by a basis `b` of `K`. -/
def heckeFamily (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ)) :
    ThetaFamily ι (Fin (rank K) → ℝ) :=
  (unitWeights K).thetaFamily b e

theorem heckeFamily_covol (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ)) :
    (heckeFamily b e).covol = |(casMatrix (fun _ => 1) b e).det| := rfl

/-- **Hecke's FE-pair** of the lattice spanned by `b`. -/
def heckeFEPair [Nonempty ι] (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ)) : WeakFEPair ℂ :=
  (heckeFamily b e).fePair (heckeMeasure K)

/-- **Functional equation** of Hecke's `Λ` for the lattice of `b` and its trace dual. -/
theorem heckeFEPair_functional_equation [Nonempty ι] (b : Module.Basis ι ℚ K)
    (e : ι ≃ (K →+* ℂ)) (s : ℂ) :
    (heckeFEPair b e).Λ ((Fintype.card ι : ℝ) / 2 - s) =
      ((|(casMatrix (fun _ => 1) b e).det|⁻¹ : ℝ) : ℂ) * (heckeFEPair b e).symm.Λ s :=
  ThetaFamily.functional_equation _ _ s

/-- Hecke's `Λ` is holomorphic away from `0` and `n/2`. -/
theorem heckeFEPair_differentiableAt [Nonempty ι] (b : Module.Basis ι ℚ K)
    (e : ι ≃ (K →+* ℂ)) {s : ℂ} (hs0 : s ≠ 0) (hsk : s ≠ ((Fintype.card ι : ℝ) / 2 : ℝ)) :
    DifferentiableAt ℂ (heckeFEPair b e).Λ s :=
  ThetaFamily.differentiableAt_Λ _ _ hs0 hsk

/-- The residue of Hecke's `Λ` at `s = n/2` is `1 / covol`. -/
theorem heckeFEPair_residue [Nonempty ι] (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ)) :
    Filter.Tendsto (fun s : ℂ => (s - ((Fintype.card ι : ℝ) / 2 : ℝ)) * (heckeFEPair b e).Λ s)
      (nhdsWithin (((Fintype.card ι : ℝ) / 2 : ℝ) : ℂ) {(((Fintype.card ι : ℝ) / 2 : ℝ) : ℂ)}ᶜ)
      (nhds ((|(casMatrix (fun _ => 1) b e).det|⁻¹ : ℝ) : ℂ)) := by
  have := ThetaFamily.residue (heckeFamily b e) (heckeMeasure K)
  rw [heckeMeasure_real_univ, heckeFamily_covol] at this
  simpa [heckeFEPair] using this

/-- **Hecke's `Λ` as an averaged Epstein zeta function of the norm forms**, for `re s > n/2`. -/
theorem heckeFEPair_eq_integral [Nonempty ι] (b : Module.Basis ι ℚ K) (e : ι ≃ (K →+* ℂ))
    {s : ℂ} (hs : (Fintype.card ι : ℝ) / 2 < s.re) :
    (heckeFEPair b e).Λ s = ∫ p in unitCube K, ∑' m : ι → ℤ,
      π ^ (-s) * Gamma s * 1 /
        ((∑ σ, (unitWeights K).y p σ * Complex.normSq (σ (∑ j, m j • b j)) : ℝ) : ℂ) ^ s := by
  rw [heckeFEPair, ThetaFamily.Λ_eq_integral _ _ hs, heckeMeasure]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [heckeFamily]
  simp_rw [WeightFamily.sqNorm_thetaFamily, WeightFamily.weightedNormSq_w]

end SimultaneousPrimitiveRoots.Hecke

end
