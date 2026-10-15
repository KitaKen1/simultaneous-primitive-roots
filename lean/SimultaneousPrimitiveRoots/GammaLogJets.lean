module

public import SimultaneousPrimitiveRoots.GammaProfileBounds
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology Convolution ContDiff
noncomputable section

/-- Negative-log Gamma jets. Every step uses only two exponent-shifted jets. -/
def artinGammaLogJet (a : ℝ) : ℕ → ℝ → ℂ
  | 0, v => artinGammaDensity a (Real.exp (-v))
  | j + 1, v => -(a : ℂ) * artinGammaLogJet a j v + artinGammaLogJet (a + 1) j v

theorem artinGammaDensity_log_exp (a v : ℝ) :
    artinGammaDensity a (Real.exp (-v)) =
      (Real.exp (-a * v - Real.exp (-v)) : ℝ) := by
  rw [artinGammaDensity_eq_ofReal _ (Real.exp_pos _),
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
  congr 2
  ring

theorem artinGammaDensity_log_shift (a v : ℝ) :
    artinGammaDensity (a + 1) (Real.exp (-v)) =
      (Real.exp (-v) : ℂ) * artinGammaDensity a (Real.exp (-v)) := by
  simp only [artinGammaDensity_log_exp, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem artinGammaDensity_log_hasDerivAt (a v : ℝ) :
    HasDerivAt (fun w => artinGammaDensity a (Real.exp (-w)))
      (-(a : ℂ) * artinGammaDensity a (Real.exp (-v)) +
        artinGammaDensity (a + 1) (Real.exp (-v))) v := by
  have h := (((hasDerivAt_id v).const_mul (-a)).sub
    ((hasDerivAt_id v).neg.exp)).exp.ofReal_comp
  simp only [id_eq, Pi.sub_apply, Pi.neg_apply, mul_one, mul_neg, sub_neg_eq_add] at h
  rw [funext (artinGammaDensity_log_exp a)]
  convert h using 1
  rw [artinGammaDensity_log_shift, artinGammaDensity_log_exp]
  push_cast
  ring

theorem artinGammaLogJet_hasDerivAt (j : ℕ) (a v : ℝ) :
    HasDerivAt (artinGammaLogJet a j) (artinGammaLogJet a (j + 1) v) v := by
  induction j generalizing a with
  | zero => exact artinGammaDensity_log_hasDerivAt a v
  | succ j ih =>
    exact ((ih a).const_mul (-(a : ℂ))).add (ih (a + 1))

theorem artinGammaLogJet_continuous (a : ℝ) (j : ℕ) :
    Continuous (artinGammaLogJet a j) :=
  (show Differentiable ℝ (artinGammaLogJet a j) from
    fun v => (artinGammaLogJet_hasDerivAt j a v).differentiableAt).continuous

theorem artinGammaLogJet_bound {a : ℝ} (ha : 0 < a) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ v, ‖artinGammaLogJet a j v‖ ≤ M := by
  induction j generalizing a with
  | zero =>
    refine ⟨Real.exp (a * Real.log a - a), Real.exp_pos _, fun v => ?_⟩
    simpa only [artinGammaLogJet, add_zero, artinGammaDensity_log_weight] using
      artinGammaDensity_log_bound (a := a) (σ := 0) (by simpa using ha) v
  | succ j ih =>
    obtain ⟨M, hM, hb⟩ := ih ha
    obtain ⟨N, hN, hc⟩ := ih (show 0 < a + 1 by linarith)
    refine ⟨‖(a : ℂ)‖ * M + N, by positivity, fun v => ?_⟩
    apply (norm_add_le _ _).trans
    simp only [norm_mul, norm_neg]
    exact add_le_add (mul_le_mul_of_nonneg_left (hb v) (norm_nonneg _)) (hc v)

/-- A certified jet chain is the actual iterated derivative, not merely a name for it. -/
theorem artinJetChain_iteratedDeriv {J : ℕ → ℝ → ℂ}
    (hJ : ∀ j v, HasDerivAt (J j) (J (j + 1) v) v) (j : ℕ) :
    iteratedDeriv j (J 0) = J j := by
  induction j with
  | zero => exact iteratedDeriv_zero
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext (fun v => (hJ j v).deriv)

theorem artinJetChain_contDiff {J : ℕ → ℝ → ℂ}
    (hJ : ∀ j v, HasDerivAt (J j) (J (j + 1) v) v) :
    ContDiff ℝ ∞ (J 0) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro j _
  rw [artinJetChain_iteratedDeriv hJ]
  exact fun v => (hJ j v).differentiableAt

theorem artinGammaDensity_log_smooth_bounded {a σ : ℝ} (ha : 0 < a + σ) :
    ContDiff ℝ ∞ (artinMellinLogPullback (artinGammaDensity a) (σ : ℂ)) ∧
      ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ v,
        ‖iteratedDeriv j (artinMellinLogPullback (artinGammaDensity a) (σ : ℂ)) v‖ ≤ M := by
  have he : artinMellinLogPullback (artinGammaDensity a) (σ : ℂ) =
      artinGammaLogJet (a + σ) 0 := funext (artinGammaDensity_log_weight a σ)
  rw [he]
  refine ⟨artinJetChain_contDiff (artinGammaLogJet_hasDerivAt · _ ·), fun j => ?_⟩
  rw [artinJetChain_iteratedDeriv (artinGammaLogJet_hasDerivAt · _ ·)]
  exact artinGammaLogJet_bound ha j

/-- Differentiate every level of an actual integral with an integrable majorant
uniform in the real parameter. The majorant may depend on the derivative order. -/
theorem artinIntegralJet_hasDerivAt {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : ℕ → ℝ → X → ℂ}
    (hm : ∀ j v, AEStronglyMeasurable (F j v) μ)
    (hb : ∀ j, ∃ B : X → ℝ, Integrable B μ ∧ ∀ᵐ x ∂μ, ∀ v, ‖F j v x‖ ≤ B x)
    (hd : ∀ j, ∀ᵐ x ∂μ, ∀ v, HasDerivAt (fun w => F j w x) (F (j + 1) v x) v)
    (j : ℕ) (v : ℝ) :
    HasDerivAt (fun w => ∫ x, F j w x ∂μ) (∫ x, F (j + 1) v x ∂μ) v := by
  obtain ⟨B, hBi, hB⟩ := hb j
  obtain ⟨B', hBi', hB'⟩ := hb (j + 1)
  have hi : Integrable (F j v) μ := hBi.mono' (hm j v) (hB.mono (fun x hx => hx v))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := univ) (Filter.univ_mem) (Filter.Eventually.of_forall (hm j)) hi
    (hm (j + 1) v) (hB'.mono (fun x hx w _ => hx w)) hBi'
    ((hd j).mono (fun x hx w _ => hx w))).2

end
end SimultaneousPrimitiveRoots
