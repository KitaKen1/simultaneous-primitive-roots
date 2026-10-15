module

public import SimultaneousPrimitiveRoots.GaussianHorizontalDecay
public import SimultaneousPrimitiveRoots.KummerQuotientRightTails
public import SimultaneousPrimitiveRoots.KummerFiniteContourMain

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Metric Filter
open scoped Topology
noncomputable section

/-- Only the real part of the actual left-edge integral must be bounded.
The chosen line may depend on a,q,x; L must be uniform in the closing route. -/
def KummerGaussianLeftEdgeUpperInput (H : ℂ → ℂ) (q : ℕ) (x L : ℝ) : Prop :=
  ∃ σ : ℝ, -1 ≤ σ ∧ σ ≤ 0 ∧ (∀ s : ℂ, s.re = σ → H s ≠ 0) ∧
    ∀ᶠ T : ℝ in atTop,
      (PNTAnd.VIntegral' (gaussianFullQuotientIntegrand H ((q : ℂ) - 1) x)
        σ (-T) T).re ≤ L * (q : ℝ) * Real.log (2 * (q : ℝ))

/-- Small horizontal edges and actual right tails reduce the finite remainder
task to a one-sided left-edge estimate. Its height threshold is not uniform. -/
theorem kummerFullQuotient_exists_finite_contour_of_left_edge {a q : ℕ}
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)] {H : ℂ → ℂ}
    (hH : NumberFieldEntireFullQuotientContinuation
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {x B L : ℝ} (hx : 1 ≤ x) (hB : 0 ≤ B)
    (hgrowth : ∀ U : ℝ, 0 ≤ U → ∀ z ∈ sphere (2 : ℂ) (2 * (U + 2)),
      ‖H z‖ ≤ Real.exp (B * (U + 3) ^ 2))
    (hleft : KummerGaussianLeftEdgeUpperInput H q x L) :
    ∃ σ T : ℝ, -1 ≤ σ ∧ σ ≤ 0 ∧ 0 ≤ T ∧
      (∀ s ∈ PNTAnd.RectangleBorder ((σ : ℂ) - Complex.I * T)
        ((2 : ℂ) + Complex.I * T), H s ≠ 0) ∧
      (gaussianFiniteContourRemainder H ((q : ℂ) - 1) x σ T).re ≤
        (L + 1) * (q : ℝ) * Real.log (2 * (q : ℝ)) := by
  obtain ⟨σ, hσ, hσ0, hline, hl⟩ := hleft
  have hr := kummerFullQuotient_right_tail_norm_eventually_le hH
    (by linarith : 0 < x) (show (0 : ℝ) < 1 / 3 by norm_num)
  obtain ⟨N, hN⟩ := (hl.and hr).exists_forall_of_atTop
  obtain ⟨T, hNT, hT, hh, hi⟩ :=
    numberFieldEntireFullQuotientContinuation_exists_small_horizontal_integrals
      (PrimeKummerField a q) (CyclotomicField q ℚ) hH
      (d := (q : ℂ) - 1) (N₀ := N) hB hx
      (show (0 : ℝ) < 1 / 3 by norm_num) hgrowth
  have hσ2 : σ ≤ 2 := by linarith
  have hedge := hi σ hσ hσ2
  have hbounds := hN T hNT.le
  refine ⟨σ, T, hσ, hσ0, hT, ?_, ?_⟩
  · intro s hs
    simp only [PNTAnd.RectangleBorder, Set.mem_union, Complex.mem_reProdIm,
      Set.mem_singleton_iff, Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im] at hs
    rcases hs with ((hs | hs) | hs) | hs
    · have hre : σ ≤ s.re ∧ s.re ≤ 2 := by
        simpa [Set.uIcc_of_le hσ2] using hs.1
      apply hh s (hσ.trans hre.1) hre.2
      have him : s.im = -T := by simpa using hs.2
      rw [him, abs_neg, abs_of_nonneg hT]
    · exact hline s (by simpa using hs.1)
    · have hre : σ ≤ s.re ∧ s.re ≤ 2 := by
        simpa [Set.uIcc_of_le hσ2] using hs.1
      apply hh s (hσ.trans hre.1) hre.2
      have him : s.im = T := by simpa using hs.2
      rw [him, abs_of_nonneg hT]
    · exact numberFieldEntireFullQuotientContinuation_boundary_ne_zero
        (PrimeKummerField a q) (CyclotomicField q ℚ) hH (by
          have hre : s.re = 2 := by simpa using hs.1
          rw [hre]; norm_num)
  · rw [gaussianFiniteContourRemainder_split_right_tails,
      Complex.add_re, Complex.add_re, Complex.sub_re]
    have hb := Complex.re_le_norm (-PNTAnd.HIntegral'
      (gaussianFullQuotientIntegrand H ((q : ℂ) - 1) x) σ 2 (-T))
    rw [Complex.neg_re, norm_neg] at hb
    have ht := Complex.re_le_norm (PNTAnd.HIntegral'
      (gaussianFullQuotientIntegrand H ((q : ℂ) - 1) x) σ 2 T)
    have hrt := Complex.re_le_norm (gaussianRightTailRemainder H ((q : ℂ) - 1) x T)
    have hqlog := prime_mul_log_twice_one_le hq.out
    nlinarith [hb.trans hedge.1, ht.trans hedge.2, hrt.trans hbounds.2, hbounds.1]

/-- This implication removes the whole finite remainder from the assumed
inputs. Actual H, uniform growth, low nonreal gap and the left bound remain. -/
theorem kummerFiniteContourUpperInputs_of_left_edge {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {x δ C L : ℝ}
    (hx : 1 ≤ x) (hC : 0 ≤ C)
    (hi : ∃ H : ℂ → ℂ,
      NumberFieldEntireFullQuotientContinuation (PrimeKummerField a q) (CyclotomicField q ℚ) H ∧
      (∀ U : ℝ, 0 ≤ U → ∀ z ∈ sphere (2 : ℂ) (2 * (U + 2)),
        ‖H z‖ ≤ Real.exp
          (C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) * (U + 3) ^ 2)) ∧
      (∀ i : fullQuotientZeroIndex H, (fullQuotientIndexedZero H i).im ≠ 0 →
        |(fullQuotientIndexedZero H i).im| ≤ 2 * (q : ℝ) ^ 2 →
          (fullQuotientIndexedZero H i).re ≤ 1 - δ) ∧
      KummerGaussianLeftEdgeUpperInput H q x L) :
    KummerFiniteContourUpperInputs a q x δ C (L + 1) := by
  obtain ⟨H, hH, hgrowth, hgap, hleft⟩ := hi
  refine ⟨H, hH, hgrowth, hgap, ?_⟩
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).two_le
  have hqm : 0 ≤ (q : ℝ) - 1 := by linarith
  have hB : 0 ≤ C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * q)
    positivity
  exact kummerFullQuotient_exists_finite_contour_of_left_edge hH hx hB hgrowth hleft

end
end SimultaneousPrimitiveRoots
