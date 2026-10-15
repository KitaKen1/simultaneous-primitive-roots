module

public import SimultaneousPrimitiveRoots.NumberFieldZetaQuotient
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain Filter
open scoped Topology
noncomputable section

/-- The actual finite Euler correction multiplying the full zeta quotient.
This definition does not assert a global continuation of that quotient. -/
def numberFieldDeletedQuotientCorrection (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (T : Finset (HeightOneSpectrum (𝓞 L))) (s : ℂ) : ℂ :=
  numberFieldDeletedZetaCorrection K S s / numberFieldDeletedZetaCorrection L T s

theorem numberFieldDeletedQuotientCorrection_ne_zero (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (T : Finset (HeightOneSpectrum (𝓞 L))) {s : ℂ} (hs : 0 < s.re) :
    numberFieldDeletedQuotientCorrection K L S T s ≠ 0 :=
  div_ne_zero (numberFieldDeletedZetaCorrection_ne_zero K S hs)
    (numberFieldDeletedZetaCorrection_ne_zero L T hs)

theorem numberFieldDeletedQuotientCorrection_analyticAt (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
    {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (numberFieldDeletedQuotientCorrection K L S T) s :=
  ((numberFieldDeletedZetaCorrection_differentiable K S).analyticAt s).div
    ((numberFieldDeletedZetaCorrection_differentiable L T).analyticAt s)
    (numberFieldDeletedZetaCorrection_ne_zero L T hs)

/-- Finite deletion contributes neither zeros nor poles in Re(s)>0. -/
theorem numberFieldDeletedQuotientCorrection_order_eq_zero (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
    {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (numberFieldDeletedQuotientCorrection K L S T) s = 0 := by
  have hc := numberFieldDeletedQuotientCorrection_analyticAt K L S T hs
  rw [hc.meromorphicOrderAt_eq,
    hc.analyticOrderAt_eq_zero.mpr (numberFieldDeletedQuotientCorrection_ne_zero K L S T hs)]
  simp

/-- This order identity applies to any proposed full quotient continuation H. -/
theorem numberFieldDeletedQuotientCorrection_mul_order (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (H : ℂ → ℂ) {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (fun z => numberFieldDeletedQuotientCorrection K L S T z * H z) s =
      meromorphicOrderAt H s :=
  meromorphicOrderAt_mul_of_ne_zero
    (numberFieldDeletedQuotientCorrection_analyticAt K L S T hs)
    (numberFieldDeletedQuotientCorrection_ne_zero K L S T hs)

/-- Use a punctured germ: raw pointwise division may differ from its removable
analytic extension at a denominator zero. -/
theorem meromorphicQuotientOrder_nonneg_of_extension (f g H : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt f s) (hg : MeromorphicAt g s)
    (hH : AnalyticAt ℂ H s)
    (hEq : (fun z => f z / g z) =ᶠ[𝓝[≠] s] H) :
    0 ≤ meromorphicOrderAt f s - meromorphicOrderAt g s := by
  rw [← meromorphicOrderAt_div hf hg]
  change 0 ≤ meromorphicOrderAt (fun z => f z / g z) s
  rw [meromorphicOrderAt_congr hEq]
  exact hH.meromorphicOrderAt_nonneg

theorem numberFieldDeletedQuotientExtension_analyticAt (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (H : ℂ → ℂ) {s : ℂ} (hs : 0 < s.re) (hH : AnalyticAt ℂ H s) :
    AnalyticAt ℂ (fun z => numberFieldDeletedQuotientCorrection K L S T z * H z) s :=
  (numberFieldDeletedQuotientCorrection_analyticAt K L S T hs).mul hH

/-- Given an actual analytic full-quotient extension, its actual finite Euler
correction cannot turn zero multiplicities into negative pole weights. The
existence of the full-quotient extension is still an explicit input. -/
theorem numberFieldDeletedQuotientExtension_order_nonneg (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (H : ℂ → ℂ) {s : ℂ} (hs : 0 < s.re) (hH : AnalyticAt ℂ H s) :
    0 ≤ meromorphicOrderAt
      (fun z => numberFieldDeletedQuotientCorrection K L S T z * H z) s := by
  rw [numberFieldDeletedQuotientCorrection_mul_order K L S T H hs]
  exact hH.meromorphicOrderAt_nonneg

/-- An algebraic identity for the actual normalized functions. It gives no
extra analytic domain beyond the continuation already constructed. -/
theorem numberFieldIncompleteZetaQuotient_eq_correction_mul_full (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (s : ℂ) :
    numberFieldIncompleteZetaQuotient K L S T s =
      numberFieldDeletedQuotientCorrection K L S T s *
        (numberFieldNormalizedZeta K s / numberFieldNormalizedZeta L s) := by
  unfold numberFieldIncompleteZetaQuotient numberFieldIncompleteZetaNormalized
    numberFieldDeletedQuotientCorrection
  rw [mul_div_mul_comm]
  ring

theorem numberFieldIncompleteZetaQuotient_order_eq_full (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
    {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (numberFieldIncompleteZetaQuotient K L S T) s =
      meromorphicOrderAt (fun z => numberFieldNormalizedZeta K z / numberFieldNormalizedZeta L z) s := by
  have heq : numberFieldIncompleteZetaQuotient K L S T =
      (fun z => numberFieldDeletedQuotientCorrection K L S T z *
        (numberFieldNormalizedZeta K z / numberFieldNormalizedZeta L z)) :=
    funext (numberFieldIncompleteZetaQuotient_eq_correction_mul_full K L S T)
  rw [heq]
  exact numberFieldDeletedQuotientCorrection_mul_order K L S T _ hs

/-- The missing full-quotient analytic extension is kept explicit. In
particular, no Aramata--Brauer existence theorem is manufactured here. -/
theorem numberFieldIncompleteZetaQuotient_order_nonneg_of_full_extension (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (H : ℂ → ℂ) {s : ℂ} (hs : 0 < s.re) (hH : AnalyticAt ℂ H s)
    (hEq : (fun z => numberFieldNormalizedZeta K z / numberFieldNormalizedZeta L z)
      =ᶠ[𝓝[≠] s] H) :
    0 ≤ meromorphicOrderAt (numberFieldIncompleteZetaQuotient K L S T) s := by
  rw [numberFieldIncompleteZetaQuotient_order_eq_full K L S T hs,
    meromorphicOrderAt_congr hEq]
  exact hH.meromorphicOrderAt_nonneg

end
end SimultaneousPrimitiveRoots
