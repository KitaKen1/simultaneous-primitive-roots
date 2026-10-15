module

public import SimultaneousPrimitiveRoots.KummerQuotientLeftRectangle
public import SimultaneousPrimitiveRoots.GaussianFiniteZeroBounds

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField Metric Classical
noncomputable section

/-- A finite critical-strip rectangle contribution is bounded directly by
positive Gaussian mass; no infinite signed explicit formula is an input. -/
theorem kummerEntireFullQuotientContinuation_criticalRectangleSignedSum_le
    {a q : ℕ} [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {C x δ σ T : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hb : ∀ U : ℝ, 0 ≤ U → ∀ z ∈ sphere (2 : ℂ) (2 * (U + 2)),
      ‖H z‖ ≤ Real.exp
        (C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) * (U + 3) ^ 2))
    (hg : ∀ i : fullQuotientZeroIndex H, (fullQuotientIndexedZero H i).im ≠ 0 →
      |(fullQuotientIndexedZero H i).im| ≤ 2 * (q : ℝ) ^ 2 →
        (fullQuotientIndexedZero H i).re ≤ 1 - δ) :
    (∑' s : {s : ℂ | s ∈ Complex.Rectangle ((σ : ℂ) - Complex.I * T)
        ((2 : ℂ) + Complex.I * T) ∧ H s = 0 ∧ 0 ≤ s.re},
      (-(fullQuotientZeroMultiplicity H s : ℂ) / ((q : ℂ) - 1)) *
        ((x : ℂ) ^ (s : ℂ) * artinGaussianMellin s)).re ≤
      artinGaussianConstant * kummerGaussianZeroMassConstant C *
        (x ^ (1 - δ) + x * Real.exp (-(q : ℝ) ^ 4 / 2)) *
        (q : ℝ) * Real.log (2 * (q : ℝ)) := by
  let z : ℂ := (σ : ℂ) - Complex.I * T
  let w : ℂ := (2 : ℂ) + Complex.I * T
  let J := {s : ℂ // s ∈ Complex.Rectangle z w ∧ H s = 0 ∧ 0 ≤ s.re}
  have hc : IsCompact (Complex.Rectangle z w) :=
    (isCompact_uIcc : IsCompact (Set.uIcc z.re w.re)).reProdIm isCompact_uIcc
  have hf : {s : ℂ | s ∈ Complex.Rectangle z w ∧ H s = 0 ∧ 0 ≤ s.re}.Finite :=
    (numberFieldEntireFullQuotientContinuation_finite_zeros_compact
      (PrimeKummerField a q) (CyclotomicField q ℚ) hH hc).subset (fun _ hs => ⟨hs.1, hs.2.1⟩)
  let : Fintype J := hf.fintype
  have hright (s : J) : s.val.re ≤ 1 := by
    by_contra hn
    exact numberFieldEntireFullQuotientContinuation_boundary_ne_zero
      (PrimeKummerField a q) (CyclotomicField q ℚ) hH
        (le_of_lt (lt_of_not_ge hn)) s.property.2.1
  let e : J ↪ {s : ℂ // 0 ≤ s.re ∧ s.re ≤ 1 ∧ H s = 0} :=
    ⟨fun s => ⟨s.val, s.property.2.2, hright s, s.property.2.1⟩,
      fun s t h => Subtype.ext (congrArg
        (fun v : {s : ℂ // 0 ≤ s.re ∧ s.re ≤ 1 ∧ H s = 0} => v.val) h)⟩
  let S := (Finset.univ : Finset J).map e
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  have hd : 0 < (q : ℝ) - 1 := by linarith
  have hm := kummerEntireFullQuotientContinuation_gaussianMass_of_boundary_growth hH hC hb
  have h := fullQuotientCriticalZeros_finite_signed_sum_le hx
    (T := 2 * (q : ℝ) ^ 2) (by positivity) hd hm.1 hg S
  simp only [Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one,
    show -(2 * (q : ℝ) ^ 2) ^ 2 / 8 = -(q : ℝ) ^ 4 / 2 by ring] at h
  have hsum : (∑' s : J, (-(fullQuotientZeroMultiplicity H s : ℂ) / ((q : ℂ) - 1)) *
      ((x : ℂ) ^ (s : ℂ) * artinGaussianMellin s)).re ≤
      (artinGaussianConstant * (x ^ (1 - δ) + x * Real.exp (-(q : ℝ) ^ 4 / 2)) /
        ((q : ℝ) - 1)) * ∑' i : fullQuotientZeroIndex H,
          Real.exp (-(fullQuotientIndexedZero H i).im ^ 2 / 8) := by
    rw [tsum_fintype]
    simpa [S, Finset.sum_map, e, artinGaussianZeroTerm] using h
  apply hsum.trans
  have hp : 0 ≤ artinGaussianConstant *
      (x ^ (1 - δ) + x * Real.exp (-(q : ℝ) ^ 4 / 2)) / ((q : ℝ) - 1) := by
    have := artinGaussianConstant_pos
    positivity
  calc
    _ ≤ (artinGaussianConstant * (x ^ (1 - δ) + x * Real.exp (-(q : ℝ) ^ 4 / 2)) /
        ((q : ℝ) - 1)) * (kummerGaussianZeroMassConstant C * (q : ℝ) *
          ((q : ℝ) - 1) * Real.log (2 * (q : ℝ))) := mul_le_mul_of_nonneg_left hm.2 hp
    _ = _ := by field_simp

end
end SimultaneousPrimitiveRoots
