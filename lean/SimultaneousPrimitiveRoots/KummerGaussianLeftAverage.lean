module

public import SimultaneousPrimitiveRoots.NegativeStripLineAverage
public import SimultaneousPrimitiveRoots.KummerLeftEdgeContour

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Metric Filter
noncomputable section

def kummerGaussianLeftSpatialConstant (C : ℝ) : ℝ :=
  artinGaussianConstant * Real.pi *
    (diskLogDerivativeConstant + 3 / Real.log (3 / 2)) * (5 + 9 * C) *
      gaussianLeftSpatialConstant

def kummerGaussianLeftAverageConstant (C : ℝ) : ℝ :=
  kummerGaussianLeftSpatialConstant C / (2 * Real.pi)

theorem kummerGaussianLeftSpatialConstant_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ kummerGaussianLeftSpatialConstant C := by
  unfold kummerGaussianLeftSpatialConstant
  have := artinGaussianConstant_pos
  have := diskLogDerivativeConstant_pos
  have := Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)
  have := gaussianLeftSpatialConstant_nonneg
  positivity

theorem kummerGaussianLeftAverageConstant_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ kummerGaussianLeftAverageConstant C :=
  div_nonneg (kummerGaussianLeftSpatialConstant_nonneg hC) (by positivity)

/-- No quantitative separation of the chosen line is needed: its actual L1
norm is bounded by the spatial average, and all actual zeros are avoided. -/
theorem numberFieldEntireFullQuotientContinuation_exists_left_line_norm_integral_le
    (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K E H)
    {B : ℝ} (hB : 0 ≤ B)
    (hgrowth : ∀ U : ℝ, 0 ≤ U → ∀ z ∈ sphere (2 : ℂ) (2 * (U + 2)),
      ‖H z‖ ≤ Real.exp (B * (U + 3) ^ 2)) {x : ℝ} (hx : 1 ≤ x) (d : ℂ) :
    ∃ σ : ℝ, -1 ≤ σ ∧ σ ≤ 0 ∧ (∀ s : ℂ, s.re = σ → H s ≠ 0) ∧
      Integrable (fun y : ℝ => gaussianFullQuotientIntegrand H d x
        ((σ : ℂ) + y * Complex.I)) ∧
      (∫ y : ℝ, ‖gaussianFullQuotientIntegrand H d x ((σ : ℂ) + y * Complex.I)‖) ≤
        (artinGaussianConstant * quotientLeftSpatialConstant B (Module.finrank ℚ E : ℝ) / ‖d‖) *
          gaussianLeftSpatialConstant := by
  obtain ⟨hf, hb⟩ := numberFieldEntireFullQuotientContinuation_gaussian_left_spatial_integral_le
    K E hH hB hgrowth hx d
  have hc := (numberFieldEntireFullQuotientContinuation_countable_zeros K E hH).image Complex.re
  obtain ⟨σ, hσ, hσ0, hz, hi, hh⟩ := exists_negative_line_integrable_norm_le hf hc
  refine ⟨σ, hσ, hσ0, ?_, hi, hh.trans hb⟩
  intro s hs hzero
  exact hz ⟨s, hzero, hs⟩

theorem normalizedVerticalIntegral_norm_le_of_integrable {f : ℂ → ℂ} {σ : ℝ}
    (hf : Integrable (fun y : ℝ => f ((σ : ℂ) + y * Complex.I))) (a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => f ((σ : ℂ) + y * Complex.I)) volume a b ∧
      ‖PNTAnd.VIntegral' f σ a b‖ ≤
        (1 / (2 * Real.pi)) * ∫ y : ℝ, ‖f ((σ : ℂ) + y * Complex.I)‖ := by
  refine ⟨hf.intervalIntegrable, ?_⟩
  have hi := (intervalIntegral.norm_integral_le_integral_norm_uIoc
    (f := fun y : ℝ => f ((σ : ℂ) + y * Complex.I)) (a := a) (b := b)).trans
    (setIntegral_le_integral (s := Set.uIoc a b) hf.norm
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _)))
  have hn : ‖(1 : ℂ) / (2 * Real.pi * Complex.I)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, mul_one]
  unfold PNTAnd.VIntegral' PNTAnd.VIntegral
  rw [norm_smul, norm_smul, hn, Complex.norm_I, one_mul]
  exact mul_le_mul_of_nonneg_left hi (by positivity)

/-- The spatial estimate becomes a family-uniform O(q log(2q)) estimate after
normalization by q-1. The supplied uniform growth coefficient is retained. -/
theorem kummerEntireFullQuotientContinuation_leftSpatialIntegral_le
    {a q : ℕ} [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {C x : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hb : ∀ U : ℝ, 0 ≤ U → ∀ z ∈ sphere (2 : ℂ) (2 * (U + 2)),
      ‖H z‖ ≤ Real.exp
        (C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) * (U + 3) ^ 2)) :
    (artinGaussianConstant *
      quotientLeftSpatialConstant
        (C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)))
        (Module.finrank ℚ (CyclotomicField q ℚ) : ℝ) / ‖(q : ℂ) - 1‖) *
          gaussianLeftSpatialConstant ≤
      kummerGaussianLeftSpatialConstant C * (q : ℝ) * Real.log (2 * (q : ℝ)) := by
  let : NeZero q := ⟨hq.out.ne_zero⟩
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  have hqm : 1 ≤ (q : ℝ) - 1 := by linarith
  have hqm0 : 0 < (q : ℝ) - 1 := by linarith
  have hR := prime_mul_log_twice_one_le hq.out
  have hn : ‖(q : ℂ) - 1‖ = (q : ℝ) - 1 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_of_nonneg hqm0.le]
  rw [prime_cyclotomic_degree (E := CyclotomicField q ℚ) hq.out,
    Nat.cast_sub hq.out.one_lt.le, Nat.cast_one, hn]
  have hcost : (1 + 9 * (C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ))) +
      4 * ((q : ℝ) - 1)) / ((q : ℝ) - 1) ≤
        (5 + 9 * C) * (q : ℝ) * Real.log (2 * (q : ℝ)) := by
    apply (div_le_iff₀ hqm0).mpr
    have hh := mul_le_mul_of_nonneg_left hR hqm0.le
    have hh1 : 1 ≤ (q : ℝ) * Real.log (2 * (q : ℝ)) * ((q : ℝ) - 1) := by
      nlinarith only [hh, hqm]
    nlinarith only [hh, hh1]
  have hP : 0 ≤ artinGaussianConstant * Real.pi *
      (diskLogDerivativeConstant + 3 / Real.log (3 / 2)) * gaussianLeftSpatialConstant := by
    have := artinGaussianConstant_pos
    have := diskLogDerivativeConstant_pos
    have := Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)
    have := gaussianLeftSpatialConstant_nonneg
    positivity
  have hh := mul_le_mul_of_nonneg_left hcost hP
  convert hh using 1 <;> (try rfl) <;> dsimp [quotientLeftSpatialConstant, kummerGaussianLeftSpatialConstant] <;> ring

/-- The previously open actual left-edge input follows from the actual entire
continuation and uniform boundary growth, with an explicit uniform constant. -/
theorem kummerGaussianLeftEdgeUpperInput_of_boundary_growth
    {a q : ℕ} [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {C x : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hb : ∀ U : ℝ, 0 ≤ U → ∀ z ∈ sphere (2 : ℂ) (2 * (U + 2)),
      ‖H z‖ ≤ Real.exp
        (C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) * (U + 3) ^ 2)) :
    KummerGaussianLeftEdgeUpperInput H q x (kummerGaussianLeftAverageConstant C) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  have hB : 0 ≤ C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) := by
    have hqm : 0 ≤ (q : ℝ) - 1 := by linarith
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * q)
    positivity
  obtain ⟨σ, hσ, hσ0, hline, hi, hh⟩ :=
    numberFieldEntireFullQuotientContinuation_exists_left_line_norm_integral_le
      (PrimeKummerField a q) (CyclotomicField q ℚ) hH hB hb hx ((q : ℂ) - 1)
  have hbound := hh.trans (kummerEntireFullQuotientContinuation_leftSpatialIntegral_le hH hC hx hb)
  refine ⟨σ, hσ, hσ0, hline, Filter.Eventually.of_forall (fun T => ?_)⟩
  have hv := (normalizedVerticalIntegral_norm_le_of_integrable hi (-T) T).2
  have hh' := (Complex.re_le_norm _).trans (hv.trans
    (mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 1 / (2 * Real.pi))))
  convert hh' using 1 <;> (try rfl) <;> unfold kummerGaussianLeftAverageConstant <;> ring

end
end SimultaneousPrimitiveRoots
