module

public import SimultaneousPrimitiveRoots.KummerFiniteContourBound
public import SimultaneousPrimitiveRoots.Explicit.EntireZeroData
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientMultiplicity
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.KummerUniformDeletionBridge
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroInputs
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientZeroCount
public import SimultaneousPrimitiveRoots.Explicit.GaussianZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientLogResidue
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientContourChoice
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientRectangle
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientLeftZeroCount
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientFiniteFormula
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientLeftZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientLeftRectangle
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientFiniteUpper

/-! Generalization of `SimultaneousPrimitiveRoots.KummerFiniteContourBound` from the entire zeta quotient
to abstract `EntireZeroData` (machine-copied; only declarations depending on the quotient
hypothesis are restated). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open NumberField Metric Classical
noncomputable section

/-- A single finite contour with a one-sided remainder bound suffices for the
actual full trace upper bound. No infinite-height signed formula is required. -/
theorem kummerFullQuotient_finite_contour_trace_le
    {a q : ℕ} [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    {H : ℂ → ℂ} (hH : EntireZeroData
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {C x δ σ T R : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x) (hδ : δ ≤ 1) (hR : 0 ≤ R)
    (hσ : -1 ≤ σ) (hσ0 : σ ≤ 0) (hT : 0 ≤ T)
    (hb : ∀ U : ℝ, 0 ≤ U → ∀ z ∈ sphere (2 : ℂ) (2 * (U + 2)),
      ‖H z‖ ≤ Real.exp
        (C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) * (U + 3) ^ 2))
    (hg : ∀ i : fullQuotientZeroIndex H, (fullQuotientIndexedZero H i).im ≠ 0 →
      |(fullQuotientIndexedZero H i).im| ≤ 2 * (q : ℝ) ^ 2 →
        (fullQuotientIndexedZero H i).re ≤ 1 - δ)
    (hborder : ∀ s ∈ PNTAnd.RectangleBorder ((σ : ℂ) - Complex.I * T)
      ((2 : ℂ) + Complex.I * T), H s ≠ 0)
    (hrem : (gaussianFiniteContourRemainder H ((q : ℂ) - 1) x σ T).re ≤
      R * (q : ℝ) * Real.log (2 * (q : ℝ))) :
    primeKummerGaussianFullSignedTrace a q x ≤
      (3 * artinGaussianConstant * kummerGaussianZeroMassConstant C + R) *
        x ^ (1 - δ) * (q : ℝ) * Real.log (2 * (q : ℝ)) +
      artinGaussianConstant * kummerGaussianZeroMassConstant C *
        x * (q : ℝ) * Real.log (2 * (q : ℝ)) * Real.exp (-(q : ℝ) ^ 4 / 2) := by
  have hr := kummerFullQuotient_finite_gaussian_formula hH
    (by linarith : 0 < x) (by linarith : σ ≤ 2) hT hborder
  have hc : IsCompact (Complex.Rectangle ((σ : ℂ) - Complex.I * T)
      ((2 : ℂ) + Complex.I * T)) :=
    (isCompact_uIcc : IsCompact (Set.uIcc _ _)).reProdIm isCompact_uIcc
  have hf := numberFieldEntireFullQuotientContinuation_finite_zeros_compact
    (PrimeKummerField a q) (CyclotomicField q ℚ) hH hc
  have hsplit := finiteZeroResidueSum_split
    (fun s => s ∈ Complex.Rectangle ((σ : ℂ) - Complex.I * T) ((2 : ℂ) + Complex.I * T))
    (fun s => H s = 0) hf
    (fun s => (-(fullQuotientZeroMultiplicity H s : ℂ) / ((q : ℂ) - 1)) *
      ((x : ℂ) ^ s * artinGaussianMellin s))
  change (primeKummerGaussianFullSignedTrace a q x : ℂ) =
    (∑' s : {s : ℂ // s ∈ Complex.Rectangle ((σ : ℂ) - Complex.I * T)
        ((2 : ℂ) + Complex.I * T) ∧ H s = 0},
      (-(fullQuotientZeroMultiplicity H s : ℂ) / ((q : ℂ) - 1)) *
        ((x : ℂ) ^ (s : ℂ) * artinGaussianMellin s)) +
      gaussianFiniteContourRemainder H ((q : ℂ) - 1) x σ T at hr
  rw [hsplit] at hr
  have hr' := congrArg Complex.re hr
  simp only [Complex.ofReal_re, Complex.add_re] at hr'
  have hl := kummerEntireFullQuotientContinuation_leftRectangleSignedSum_le
    hH hC hx hσ (by linarith : σ ≤ 2) hT hb
  have hu := kummerEntireFullQuotientContinuation_criticalRectangleSignedSum_le
    hH hC hx (σ := σ) (T := T) hb hg
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  have hM := kummerGaussianZeroMassConstant_nonneg hC
  have hpos := artinGaussianConstant_pos.le
  have hp : 1 ≤ x ^ (1 - δ) := Real.one_le_rpow hx (by linarith)
  have hsmall := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (2 * artinGaussianConstant * kummerGaussianZeroMassConstant C + R) *
      (q : ℝ) * Real.log (2 * (q : ℝ)) by positivity)
  change primeKummerGaussianFullSignedTrace a q x = _ at hr'
  have htotal := hr'.le.trans (add_le_add (add_le_add hl hu) hrem)
  nlinarith only [htotal, hsmall]

end
end SimultaneousPrimitiveRoots.Explicit
