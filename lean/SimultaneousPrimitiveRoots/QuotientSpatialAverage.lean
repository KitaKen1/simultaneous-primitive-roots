module

public import SimultaneousPrimitiveRoots.FinitePrincipalPartAverage
public import SimultaneousPrimitiveRoots.QuotientDiskLogDerivative
public import SimultaneousPrimitiveRoots.HorizontalQuotientGrowth

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Metric MeasureTheory Set
noncomputable section
open Classical

/-- Actual logarithmic derivatives are spatially integrable even across their
finite singularities, and their L1 bound uses multiplicity rather than separation. -/
theorem numberFieldEntireFullQuotientContinuation_logDeriv_spatial_integral_le
    (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K E H)
    {D M : ℝ} (hD : 0 < D) (hM : 0 ≤ M)
    (hb : ∀ z ∈ sphere (2 : ℂ) D, ‖H z‖ ≤ Real.exp M)
    {S : Set ℂ} (hS : MeasurableSet S) (hvol : volume S ≠ ⊤)
    (hsub : S ⊆ closedBall (2 : ℂ) (D / 4)) :
    IntegrableOn (fun s : ℂ => deriv H s / H s) S ∧
      (∫ s : ℂ in S, ‖deriv H s / H s‖) ≤
        (diskLogDerivativeConstant * (volume S).toReal / D +
          (2 * Real.pi + (volume S).toReal) / Real.log (3 / 2)) *
            (1 + M + 4 * (Module.finrank ℚ E : ℝ)) := by
  let g := fullQuotientDiskNormalization H D
  let A : ℝ := 1 + M + 4 * (Module.finrank ℚ E : ℝ)
  let hf := fullQuotientDiskNormalization_finite_zeros K E hH hD
  let F := (PNTAnd.DiskLogDerivative.finiteSetOfZeros_mono
    (by norm_num : (1 / 2 : ℝ) < 1) hf).toFinset
  let c : ℂ → ℂ := fun ρ => 2 + (D : ℂ) * ρ
  let Q : ℂ → ℂ := fun s => ∑ ρ ∈ F, (analyticOrderNatAt g ρ : ℂ) / (s - c ρ)
  have hA : 0 < A := by dsimp [A]; positivity
  have hDc : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD.ne'
  have hlog : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hb' : ∀ w : ℂ, ‖w‖ ≤ (3 / 4 : ℝ) → ‖g w‖ ≤ Real.exp A := by
    intro w hw
    apply (fullQuotientDiskNormalization_norm_bound K E hH hD hb (by linarith)).trans
    apply Real.exp_le_exp.mpr
    dsimp [A]; linarith
  have hcount : (∑ ρ ∈ F, (analyticOrderNatAt g ρ : ℝ)) ≤ A / Real.log (3 / 2) := by
    have hh := PNTAnd.DiskLogDerivative.ZerosBound
      (B := Real.exp A) (r := 1 / 2) (R := 3 / 4) (f := g)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ((fullQuotientDiskNormalization_analytic K E hH D).mono (Set.subset_univ _))
      (fullQuotientDiskNormalization_zero K E hH D) hf hb'
    simpa only [Real.log_exp, show ((3 / 4 : ℝ) / (1 / 2)) = 3 / 2 by norm_num,
      Nat.cast_sum, one_div_mul_eq_div] using hh
  have hp : ∀ s ∈ S,
      ‖deriv H s / H s‖ ≤ diskLogDerivativeConstant * A / D + ‖Q s‖ := by
    intro s hs
    by_cases hn : H s = 0
    · rw [hn, div_zero, norm_zero]
      have := diskLogDerivativeConstant_pos
      positivity
    · let z : ℂ := (s - 2) / D
      have hz : ‖z‖ ≤ 1 / 4 := by
        dsimp [z]
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hD.le, div_le_iff₀ hD]
        have hh := hsub hs
        rw [mem_closedBall, dist_eq_norm] at hh
        linarith
      have heq : 2 + (D : ℂ) * z = s := by dsimp [z]; field_simp; ring
      have hsumeq : (∑ ρ ∈ F, (analyticOrderNatAt g ρ : ℂ) / (z - ρ)) =
          (D : ℂ) * Q s := by
        dsimp [Q, c]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ρ _
        have ht : s - (2 + (D : ℂ) * ρ) = (D : ℂ) * (z - ρ) := by rw [← heq]; ring
        rw [ht, ← mul_div_assoc, mul_div_mul_left _ _ hDc]
      have hh := fullQuotientDiskNormalization_logDeriv_principal_parts_le K E hH hD hM hb hz
        (by
          have htwo := numberFieldFullQuotientContinuation_ne_zero_two K E
            (numberFieldEntireFullQuotientContinuation_positive K E hH)
          dsimp [g, fullQuotientDiskNormalization]
          exact div_ne_zero (by rwa [heq]) htwo)
      change ‖deriv g z / g z - ∑ ρ ∈ F, (analyticOrderNatAt g ρ : ℂ) / (z - ρ)‖ ≤
        diskLogDerivativeConstant * A at hh
      rw [fullQuotientDiskNormalization_logDeriv_scale K E hH D (by rwa [heq]),
        heq, hsumeq, ← mul_sub, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hD.le] at hh
      have hpr : ‖deriv H s / H s - Q s‖ ≤ diskLogDerivativeConstant * A / D :=
        (le_div_iff₀ hD).mpr (by simpa only [mul_comm] using hh)
      exact (norm_le_norm_sub_add _ _).trans (add_le_add hpr le_rfl)
  have hQ : IntegrableOn Q S :=
    finitePrincipalParts_integrableOn hS hvol F (analyticOrderNatAt g) c
  have hc : IntegrableOn (fun _ : ℂ => diskLogDerivativeConstant * A / D) S :=
    integrableOn_const hvol
  have hmaj : IntegrableOn (fun s : ℂ => diskLogDerivativeConstant * A / D + ‖Q s‖) S :=
    hc.add hQ.norm
  have hmeas : Measurable (fun s : ℂ => deriv H s / H s) :=
    hH.1.deriv.continuous.measurable.div hH.1.continuous.measurable
  have hi : IntegrableOn (fun s : ℂ => deriv H s / H s) S :=
    hmaj.mono' hmeas.aestronglyMeasurable.restrict
      (by filter_upwards [self_mem_ae_restrict hS] with s hs; exact hp s hs)
  refine ⟨hi, ?_⟩
  have hu := setIntegral_mono_on hi.norm hmaj hS hp
  rw [integral_add hc hQ.norm, integral_const, smul_eq_mul] at hu
  simp only [Measure.real, Measure.restrict_apply_univ] at hu
  have hQI := finitePrincipalParts_norm_integral_le hS hvol F (analyticOrderNatAt g) c
  have hQI' : (∫ s : ℂ in S, ‖Q s‖) ≤
      (2 * Real.pi + (volume S).toReal) * (A / Real.log (3 / 2)) :=
    hQI.trans (mul_le_mul_of_nonneg_left hcount (by positivity))
  calc _ ≤ (volume S).toReal * (diskLogDerivativeConstant * A / D) +
      (2 * Real.pi + (volume S).toReal) * (A / Real.log (3 / 2)) :=
        hu.trans (add_le_add le_rfl hQI')
    _ = _ := by dsimp [A]; ring

end
end SimultaneousPrimitiveRoots
