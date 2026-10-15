module

public import SimultaneousPrimitiveRoots.KummerQuotientFiniteFormula
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

/-! Generalization of `SimultaneousPrimitiveRoots.KummerQuotientFiniteFormula` from the entire zeta quotient
to abstract `EntireZeroData` (machine-copied; only declarations depending on the quotient
hypothesis are restated). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open NumberField Filter Metric MeasureTheory
open scoped Topology
noncomputable section
open Classical

theorem kummerFullQuotient_verticalIntegral_eq_trace {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {H : ℂ → ℂ}
    (hH : EntireZeroData
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {x : ℝ} (hx : 0 < x) :
    PNTAnd.VerticalIntegral' (gaussianFullQuotientIntegrand H ((q : ℂ) - 1) x) 2 =
      (primeKummerGaussianFullSignedTrace a q x : ℂ) := by
  unfold PNTAnd.VerticalIntegral' PNTAnd.VerticalIntegral
  simp only [smul_eq_mul]
  change (1 / (2 * Real.pi * Complex.I)) * (Complex.I *
    (∫ y : ℝ, gaussianDirichletVerticalKernel x 2 y *
      fullQuotientSignedLogDerivative H ((q : ℂ) - 1) (((2 : ℝ) : ℂ) + y * Complex.I))) = _
  rw [kummerFullQuotientSignedLogDerivative_integral hH hx (σ := 2) (by norm_num)]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- Exact finite-height explicit formula for the actual full signed prime sum.
The remaining analytic task is to estimate the displayed actual remainder. -/
theorem kummerFullQuotient_finite_gaussian_formula {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {H : ℂ → ℂ}
    (hH : EntireZeroData
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {x σ T : ℝ} (hx : 0 < x) (hσ : σ ≤ 2) (hT : 0 ≤ T)
    (hb : ∀ s ∈ PNTAnd.RectangleBorder ((σ : ℂ) - Complex.I * T)
      ((2 : ℂ) + Complex.I * T), H s ≠ 0) :
    (primeKummerGaussianFullSignedTrace a q x : ℂ) =
      (∑' s : {s : ℂ | s ∈ Complex.Rectangle ((σ : ℂ) - Complex.I * T)
          ((2 : ℂ) + Complex.I * T) ∧ H s = 0},
        (-(fullQuotientZeroMultiplicity H s : ℂ) / ((q : ℂ) - 1)) *
          ((x : ℂ) ^ (s : ℂ) * artinGaussianMellin s)) +
      gaussianFiniteContourRemainder H ((q : ℂ) - 1) x σ T := by
  have hq : 1 < q := by have := (Fact.out : 2 ≤ a); have := (Fact.out : a < q); omega
  have hd : (q : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hq.ne')
  let f := gaussianFullQuotientIntegrand H ((q : ℂ) - 1) x
  have hInt : Integrable (fun y : ℝ => f (((2 : ℝ) : ℂ) + y * Complex.I)) :=
    kummerFullQuotientSignedLogDerivative_integrable hH hx (σ := 2) (by norm_num)
  have hr := numberFieldEntireFullQuotientContinuation_gaussian_rectangle_residue_sum
    (PrimeKummerField a q) (CyclotomicField q ℚ) hH hx hd
    (z := (σ : ℂ) - Complex.I * T) (w := (2 : ℂ) + Complex.I * T)
    (by simpa using hσ) (by simpa using (show -T ≤ T by linarith)) hb
  simp only [PNTAnd.RectangleIntegral', PNTAnd.RectangleIntegral, smul_eq_mul,
    Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_mul, one_mul,
    sub_zero, add_zero, zero_add, zero_sub] at hr
  simp only [show (2 : ℂ).re = (2 : ℝ) by norm_num,
    show (2 : ℂ).im = (0 : ℝ) by norm_num, zero_add] at hr
  rw [← kummerFullQuotient_verticalIntegral_eq_trace hH hx]
  unfold PNTAnd.VerticalIntegral'
  change (1 / (2 * Real.pi * Complex.I)) • PNTAnd.VerticalIntegral f 2 = _
  rw [PNTAnd.verticalIntegral_split_three (-T) T hInt]
  simp only [gaussianFiniteContourRemainder, PNTAnd.VIntegral', PNTAnd.HIntegral', smul_eq_mul]
  dsimp only [f]
  linear_combination hr

/-- The finite formula is available at arbitrarily high zero-free contours,
with one fixed negative left edge. This does not estimate their remainder. -/
theorem kummerFullQuotient_exists_finite_gaussian_formulas {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {H : ℂ → ℂ}
    (hH : EntireZeroData
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {x : ℝ} (hx : 0 < x) :
    ∃ σ : ℝ, -1 < σ ∧ σ < -(1 / 2 : ℝ) ∧ ∀ N : ℝ, 0 ≤ N →
      ∃ T : ℝ, N < T ∧ T < N + 1 ∧
        (primeKummerGaussianFullSignedTrace a q x : ℂ) =
          (∑' s : {s : ℂ | s ∈ Complex.Rectangle ((σ : ℂ) - Complex.I * T)
              ((2 : ℂ) + Complex.I * T) ∧ H s = 0},
            (-(fullQuotientZeroMultiplicity H s : ℂ) / ((q : ℂ) - 1)) *
              ((x : ℂ) ^ (s : ℂ) * artinGaussianMellin s)) +
          gaussianFiniteContourRemainder H ((q : ℂ) - 1) x σ T := by
  obtain ⟨σ, hl, hr, hc⟩ :=
    numberFieldEntireFullQuotientContinuation_exists_zero_free_rectangles
      (PrimeKummerField a q) (CyclotomicField q ℚ) hH
  refine ⟨σ, hl, hr, ?_⟩
  intro N hN
  obtain ⟨T, hNT, hT, hb⟩ := hc N hN
  exact ⟨T, hNT, hT, kummerFullQuotient_finite_gaussian_formula hH hx
    (by linarith) (hN.trans hNT.le) hb⟩

end
end SimultaneousPrimitiveRoots.Explicit
