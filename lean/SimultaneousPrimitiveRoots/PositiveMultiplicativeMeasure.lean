module

public import SimultaneousPrimitiveRoots.MellinProbeContinuation
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section

/-- The actual measure dT/T on the positive real axis. -/
def artinPositiveMultiplicativeMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun T : ℝ => ENNReal.ofReal T⁻¹)

theorem artinMultiplicativeDensity_measurable :
    Measurable (fun T : ℝ => ENNReal.ofReal T⁻¹) := by
  fun_prop

theorem artinPositiveMultiplicative_ae_pos :
    ∀ᵐ T ∂artinPositiveMultiplicativeMeasure, 0 < T := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem measurableSet_Ioi)

theorem artinPositiveMultiplicative_integrable_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    Integrable f artinPositiveMultiplicativeMeasure ↔
      IntegrableOn (fun T => T⁻¹ • f T) (Ioi 0) := by
  unfold artinPositiveMultiplicativeMeasure IntegrableOn
  rw [integrable_withDensity_iff_integrable_smul' artinMultiplicativeDensity_measurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hT.le)]

theorem artinPositiveMultiplicative_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    (∫ T, f T ∂artinPositiveMultiplicativeMeasure) =
      ∫ T in Ioi 0, T⁻¹ • f T := by
  unfold artinPositiveMultiplicativeMeasure
  rw [integral_withDensity_eq_integral_toReal_smul artinMultiplicativeDensity_measurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hT.le)]

/-- Logarithmic substitution absorbs exactly the density dT/T. -/
theorem artinPositiveMultiplicative_integral_exp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    (∫ T, f T ∂artinPositiveMultiplicativeMeasure) = ∫ u : ℝ, f (Real.exp u) := by
  rw [artinPositiveMultiplicative_integral, ← integral_comp_exp]
  simp only [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]

theorem artinPositiveMultiplicative_integrable_exp_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    Integrable f artinPositiveMultiplicativeMeasure ↔
      Integrable (fun u : ℝ => f (Real.exp u)) := by
  rw [artinPositiveMultiplicative_integrable_iff, ← integrable_comp_exp]
  simp only [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]

/-- Absolute moment in the actual positive multiplicative measure.
Its integral is useful only once the corresponding integrability is proved. -/
def artinKernelMoment (κ : ℝ → ℂ) (σ : ℝ) : ℝ :=
  ∫ T, T ^ σ * ‖κ T‖ ∂artinPositiveMultiplicativeMeasure

theorem artinKernelMoment_nonneg (κ : ℝ → ℂ) (σ : ℝ) : 0 ≤ artinKernelMoment κ σ := by
  apply integral_nonneg_of_ae
  filter_upwards [artinPositiveMultiplicative_ae_pos] with T hT
  exact mul_nonneg (Real.rpow_nonneg hT.le _) (norm_nonneg _)

theorem artinKernelMoment_integrable_iff (κ : ℝ → ℂ) (σ : ℝ) :
    Integrable (fun T => T ^ σ * ‖κ T‖) artinPositiveMultiplicativeMeasure ↔
      IntegrableOn (fun T => T ^ (σ - 1) * ‖κ T‖) (Ioi 0) := by
  rw [artinPositiveMultiplicative_integrable_iff]
  unfold IntegrableOn
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add hT]
  congr 2
  ring

theorem artinKernelMoment_lebesgue (κ : ℝ → ℂ) (σ : ℝ) :
    artinKernelMoment κ σ = ∫ T in Ioi 0, T ^ (σ - 1) * ‖κ T‖ := by
  rw [artinKernelMoment, artinPositiveMultiplicative_integral]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add hT]
  congr 2
  ring

/-- Only the paper's order-zero endpoint bound is needed for all moments.
This condition does not assert the construction of its reciprocal-gamma kernel. -/
def ReflectionKernelDecay (κ : ℝ → ℂ) : Prop :=
  ContinuousOn κ (Ioi 0) ∧ ∀ N : ℝ, 0 < N →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
      ‖κ T‖ ≤ C * min (T ^ N) (T ^ (-N))

/-- Choosing N=|sigma|+1 eliminates the need to assume all absolute moments. -/
theorem reflectionKernelDecay_moment_integrable {κ : ℝ → ℂ}
    (hκ : ReflectionKernelDecay κ) (σ : ℝ) :
    Integrable (fun T => T ^ σ * ‖κ T‖) artinPositiveMultiplicativeMeasure := by
  let N := |σ| + 1
  have hN : 0 < N := by dsimp [N]; positivity
  obtain ⟨C, hC, hb⟩ := hκ.2 N hN
  have htop : (fun T => ‖κ T‖) =O[atTop] (fun T : ℝ => T ^ (-N)) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simpa only [norm_norm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg hT.le _)]
      using (hb T hT).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC)
  have hbot : (fun T => ‖κ T‖) =O[𝓝[>] (0 : ℝ)] (fun T : ℝ => T ^ (-(-N))) := by
    apply IsBigO.of_bound C
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with T hT
    simpa only [norm_norm, neg_neg, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg hT.le _)]
      using (hb T hT).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hC)
  apply (artinKernelMoment_integrable_iff κ σ).mpr
  apply mellin_convergent_of_isBigO_scalar (a := N) (b := -N)
    (hκ.1.norm.locallyIntegrableOn measurableSet_Ioi) htop _ hbot
  · dsimp [N]
    linarith [le_abs_self σ, neg_abs_le σ]
  · dsimp [N]
    linarith [le_abs_self σ, neg_abs_le σ]

end
end SimultaneousPrimitiveRoots
