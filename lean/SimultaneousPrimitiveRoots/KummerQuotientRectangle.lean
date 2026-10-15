module

public import SimultaneousPrimitiveRoots.AnalyticSimplePoles
public import SimultaneousPrimitiveRoots.KummerQuotientLogResidue
public import PNTAnd.ResidueCalcOnRectangles

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField Filter Metric MeasureTheory
open scoped Topology
noncomputable section
open Classical

theorem gaussianQuotientContourKernel_analyticAt {x : ℝ} (hx : 0 < x) (s : ℂ) :
    AnalyticAt ℂ (gaussianQuotientContourKernel x) s := by
  have hn : ((1 / x : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (one_div_ne_zero hx.ne')
  have hm : Differentiable ℂ artinGaussianMellin := by
    unfold artinGaussianMellin
    fun_prop
  exact (((differentiable_id.neg.const_cpow (Or.inl hn)).mul hm).analyticAt s)

theorem gaussianQuotientContourKernel_ne_zero {x : ℝ} (hx : 0 < x) (s : ℂ) :
    gaussianQuotientContourKernel x s ≠ 0 := by
  rw [gaussianQuotientContourKernel_eq hx]
  apply mul_ne_zero
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne')
      (Complex.exp_ne_zero _)

theorem numberFieldEntireFullQuotientContinuation_signedLogDerivative_simple_poles
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) (d : ℂ) :
    PNTAnd.HasSimplePolesOn (fullQuotientSignedLogDerivative H d) Set.univ := by
  intro s _
  obtain ⟨g, hg, heq⟩ :=
    numberFieldEntireFullQuotientContinuation_signedLogDerivative_principal_part K L hH d s
  exact meromorphicOrderAt_ge_neg_one_of_principal_part hg heq

/-- The poles are the actual H-zeros, even when these zeros have multiplicity greater than one. -/
theorem numberFieldEntireFullQuotientContinuation_signedLogDerivative_pole_iff
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {d : ℂ} (hd : d ≠ 0) (s : ℂ) :
    meromorphicOrderAt (fullQuotientSignedLogDerivative H d) s < 0 ↔ H s = 0 := by
  constructor
  · intro hp
    by_contra hn
    have ha : AnalyticAt ℂ (fullQuotientSignedLogDerivative H d) s :=
      (((hH.1 s (Set.mem_univ _)).deriv.div (hH.1 s (Set.mem_univ _)) hn).neg).div_const
    exact (not_lt_of_ge ha.meromorphicOrderAt_nonneg) hp
  · intro hz
    have hm : 0 < fullQuotientZeroMultiplicity H s :=
      (numberFieldEntireFullQuotientContinuation_multiplicity_pos_iff K L hH s).mpr hz
    have hc : -(fullQuotientZeroMultiplicity H s : ℂ) / d ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hm.ne')) hd
    obtain ⟨g, hg, heq⟩ :=
      numberFieldEntireFullQuotientContinuation_signedLogDerivative_principal_part K L hH d s
    rw [meromorphicOrderAt_eq_neg_one_of_principal_part hg hc heq]
    exact WithTop.coe_lt_coe.mpr (show (-1 : ℤ) < 0 by decide)

def gaussianFullQuotientIntegrand (H : ℂ → ℂ) (d : ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  gaussianQuotientContourKernel x s * fullQuotientSignedLogDerivative H d s

theorem numberFieldEntireFullQuotientContinuation_gaussian_integrand_meromorphic
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {x : ℝ} (hx : 0 < x) (d : ℂ) : Meromorphic (gaussianFullQuotientIntegrand H d x) := by
  intro s
  exact (gaussianQuotientContourKernel_analyticAt hx s).meromorphicAt.mul
    (numberFieldEntireFullQuotientContinuation_signedLogDerivative_meromorphic K L hH d s)

theorem numberFieldEntireFullQuotientContinuation_gaussian_integrand_order
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {x : ℝ} (hx : 0 < x) (d s : ℂ) :
    meromorphicOrderAt (gaussianFullQuotientIntegrand H d x) s =
      meromorphicOrderAt (fullQuotientSignedLogDerivative H d) s :=
  meromorphicOrderAt_mul_of_ne_zero (gaussianQuotientContourKernel_analyticAt hx s)
    (gaussianQuotientContourKernel_ne_zero hx s)

theorem numberFieldEntireFullQuotientContinuation_gaussian_integrand_simple_poles
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {x : ℝ} (hx : 0 < x) (d : ℂ) :
    PNTAnd.HasSimplePolesOn (gaussianFullQuotientIntegrand H d x) Set.univ := by
  intro s hs
  rw [numberFieldEntireFullQuotientContinuation_gaussian_integrand_order K L hH hx d s]
  exact numberFieldEntireFullQuotientContinuation_signedLogDerivative_simple_poles K L hH d s hs

theorem numberFieldEntireFullQuotientContinuation_gaussian_integrand_pole_iff
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {x : ℝ} (hx : 0 < x) {d : ℂ} (hd : d ≠ 0) (s : ℂ) :
    meromorphicOrderAt (gaussianFullQuotientIntegrand H d x) s < 0 ↔ H s = 0 := by
  rw [numberFieldEntireFullQuotientContinuation_gaussian_integrand_order K L hH hx d s]
  exact numberFieldEntireFullQuotientContinuation_signedLogDerivative_pole_iff K L hH hd s

/-- This residue is only used after at-most-simple poles have been proved. -/
theorem numberFieldEntireFullQuotientContinuation_gaussian_integrand_residue
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {x : ℝ} (hx : 0 < x) (d s : ℂ) :
    PNTAnd.residue (gaussianFullQuotientIntegrand H d x) s =
      (-(fullQuotientZeroMultiplicity H s : ℂ) / d) *
        ((x : ℂ) ^ s * artinGaussianMellin s) :=
  PNTAnd.residue_eq_of_tendsto
    (numberFieldEntireFullQuotientContinuation_gaussian_residue K L hH hx d s)

/-- Finite contour shifting: the exact integral is the sum over every actual zero
inside the rectangle. Entire continuation is still an explicit input. -/
theorem numberFieldEntireFullQuotientContinuation_gaussian_rectangle_residue_sum
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {x : ℝ} (hx : 0 < x) {d : ℂ} (hd : d ≠ 0) {z w : ℂ}
    (hr : z.re ≤ w.re) (hi : z.im ≤ w.im)
    (hb : ∀ s ∈ PNTAnd.RectangleBorder z w, H s ≠ 0) :
    PNTAnd.RectangleIntegral' (gaussianFullQuotientIntegrand H d x) z w =
      ∑' s : {s : ℂ | s ∈ Complex.Rectangle z w ∧ H s = 0},
        (-(fullQuotientZeroMultiplicity H s : ℂ) / d) *
          ((x : ℂ) ^ (s : ℂ) * artinGaussianMellin s) := by
  have hp : {s : ℂ | meromorphicOrderAt (gaussianFullQuotientIntegrand H d x) s < 0} =
      {s : ℂ | H s = 0} := Set.ext fun s =>
    numberFieldEntireFullQuotientContinuation_gaussian_integrand_pole_iff K L hH hx hd s
  have hcompact : IsCompact (Complex.Rectangle z w) :=
    (isCompact_uIcc : IsCompact (Set.uIcc z.re w.re)).reProdIm isCompact_uIcc
  have hfinite : (Complex.Rectangle z w ∩
      {s : ℂ | meromorphicOrderAt (gaussianFullQuotientIntegrand H d x) s < 0}).Finite := by
    rw [hp]
    exact numberFieldEntireFullQuotientContinuation_finite_zeros_compact K L hH hcompact
  have hdisjoint : Disjoint (PNTAnd.RectangleBorder z w)
      {s : ℂ | meromorphicOrderAt (gaussianFullQuotientIntegrand H d x) s < 0} := by
    rw [hp, Set.disjoint_left]
    exact fun s hs hz => hb s hs hz
  rw [PNTAnd.RectangleIntegral'_eq_sumResiduesIn hr hi
    (fun s _ => numberFieldEntireFullQuotientContinuation_gaussian_integrand_meromorphic
      K L hH hx d s) hdisjoint hfinite
    ((numberFieldEntireFullQuotientContinuation_gaussian_integrand_simple_poles K L hH hx d).mono
      (Set.subset_univ _)), PNTAnd.sumResiduesIn, hp]
  exact tsum_congr fun s =>
    numberFieldEntireFullQuotientContinuation_gaussian_integrand_residue K L hH hx d s

end
end SimultaneousPrimitiveRoots
