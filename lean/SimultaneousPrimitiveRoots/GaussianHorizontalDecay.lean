module

public import SimultaneousPrimitiveRoots.GaussianHorizontalIntegral
public import SimultaneousPrimitiveRoots.HorizontalQuotientGrowth

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Metric Filter MeasureTheory
open scoped Topology
noncomputable section

/-- The height may depend on the actual field, x and tolerance. No uniform
height cutoff is needed to construct one finite contour for each input. -/
theorem numberFieldEntireFullQuotientContinuation_exists_small_horizontal_integrals
    (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K E H)
    {B x ε N₀ : ℝ} {d : ℂ} (hB : 0 ≤ B) (hx : 1 ≤ x) (hε : 0 < ε)
    (hgrowth : ∀ U : ℝ, 0 ≤ U → ∀ z ∈ sphere (2 : ℂ) (2 * (U + 2)),
      ‖H z‖ ≤ Real.exp (B * (U + 3) ^ 2)) :
    ∃ T : ℝ, N₀ < T ∧ 0 ≤ T ∧
      (∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → |s.im| = T → H s ≠ 0) ∧
      ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
        ‖PNTAnd.HIntegral' (gaussianFullQuotientIntegrand H d x) σ 2 (-T)‖ ≤ ε ∧
        ‖PNTAnd.HIntegral' (gaussianFullQuotientIntegrand H d x) σ 2 T‖ ≤ ε := by
  let C := horizontalQuotientGrowthConstant B (Module.finrank ℚ E : ℝ)
  let D := (3 / (2 * Real.pi)) * gaussianHorizontalKernelConstant * x ^ 2 * C / ‖d‖
  have hC : 0 ≤ C := horizontalQuotientGrowthConstant_nonneg hB (Nat.cast_nonneg _)
  have hsmall : ∀ᶠ N : ℝ in atTop,
      D * (N + 5) ^ 5 * Real.exp (-N ^ 2 / 4) ≤ ε := by
    have hh := gaussian_horizontal_polynomial_tendsto D
    exact (hh.eventually (gt_mem_nhds hε)).mono (fun _ h => h.le)
  obtain ⟨N, hNε, hNN⟩ := (hsmall.and (eventually_ge_atTop (max 0 N₀))).exists
  have hN : 0 ≤ N := (le_max_left _ _).trans hNN
  obtain ⟨T, hNT, _hTN, hh⟩ :=
    numberFieldEntireFullQuotientContinuation_exists_horizontal_polynomial_bound K E hH hB hN hgrowth
  have hT : 0 ≤ T := hN.trans hNT.le
  refine ⟨T, ((le_max_right _ _).trans hNN).trans_lt hNT, hT,
    (fun s hs hs2 hi => (hh s hs hs2 hi).1), ?_⟩
  intro σ hσ hσ2
  have hi : ∀ y : ℝ, |y| = T →
      ‖PNTAnd.HIntegral' (gaussianFullQuotientIntegrand H d x) σ 2 y‖ ≤ ε := by
    intro y hy
    have hedge : ∀ s : ℂ, σ ≤ s.re → s.re ≤ 2 → s.im = y →
        H s ≠ 0 ∧ ‖deriv H s / H s‖ ≤ C * (N + 5) ^ 5 := by
      intro s hs hs2 hi
      exact hh s (hσ.trans hs) hs2 (by simpa only [hi] using hy)
    have hb := (numberFieldEntireFullQuotientContinuation_horizontal_integral_le
      K E hH (d := d) hx hσ hσ2 (by positivity : 0 ≤ C * (N + 5) ^ 5) hedge).2
    have he : Real.exp (-y ^ 2 / 4) ≤ Real.exp (-N ^ 2 / 4) := by
      apply Real.exp_le_exp.mpr
      have hysq : y ^ 2 = T ^ 2 := by nlinarith [sq_abs y]
      nlinarith [mul_nonneg (by linarith : 0 ≤ T - N) (by linarith : 0 ≤ T + N)]
    apply le_trans _ hNε
    calc _ ≤ (3 / (2 * Real.pi)) *
          (gaussianHorizontalKernelConstant * x ^ 2 * Real.exp (-y ^ 2 / 4) *
            (C * (N + 5) ^ 5) / ‖d‖) := hb
      _ ≤ (3 / (2 * Real.pi)) *
          (gaussianHorizontalKernelConstant * x ^ 2 * Real.exp (-N ^ 2 / 4) *
            (C * (N + 5) ^ 5) / ‖d‖) := by
        have := gaussianHorizontalKernelConstant_pos
        gcongr
      _ = _ := by dsimp [D]; ring
  exact ⟨hi (-T) (by simp only [abs_neg, abs_of_nonneg hT]),
    hi T (abs_of_nonneg hT)⟩

end
end SimultaneousPrimitiveRoots
