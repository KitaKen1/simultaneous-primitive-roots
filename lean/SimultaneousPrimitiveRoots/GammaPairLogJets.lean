module

public import SimultaneousPrimitiveRoots.GammaLogJets

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology Convolution ContDiff
noncomputable section

def artinConvolutionJet (J : ℕ → ℝ → ℂ) (g : ℝ → ℂ) (j : ℕ) (v : ℝ) : ℂ :=
  ∫ w, J j (v - w) * g w

theorem artinConvolutionJet_hasDerivAt {J : ℕ → ℝ → ℂ} {g : ℝ → ℂ}
    (hJ : ∀ j v, HasDerivAt (J j) (J (j + 1) v) v)
    (hb : ∀ j, ∃ M, 0 < M ∧ ∀ v, ‖J j v‖ ≤ M) (hg : Integrable g)
    (j : ℕ) (v : ℝ) :
    HasDerivAt (artinConvolutionJet J g j) (artinConvolutionJet J g (j + 1) v) v := by
  have hc (j : ℕ) : Continuous (J j) :=
    (show Differentiable ℝ (J j) from fun v => (hJ j v).differentiableAt).continuous
  unfold artinConvolutionJet
  apply artinIntegralJet_hasDerivAt (F := fun j v w => J j (v - w) * g w)
  · intro j v
    exact ((hc j).comp (by fun_prop)).aestronglyMeasurable.mul hg.aestronglyMeasurable
  · intro j
    obtain ⟨M, _, hM⟩ := hb j
    refine ⟨fun w => M * ‖g w‖, hg.norm.const_mul M, ae_of_all _ (fun w v => ?_)⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  · intro j
    exact ae_of_all _ (fun w v => by
      simpa only [one_smul, Function.comp_apply, id_eq] using!
        ((hJ j (v - w)).scomp v ((hasDerivAt_id v).sub_const w)).mul_const (g w))

theorem artinConvolutionJet_bound {J : ℕ → ℝ → ℂ} {g : ℝ → ℂ}
    (hb : ∀ j, ∃ M, 0 < M ∧ ∀ v, ‖J j v‖ ≤ M) (hg : Integrable g) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ v, ‖artinConvolutionJet J g j v‖ ≤ M := by
  obtain ⟨M, _, hM⟩ := hb j
  refine ⟨max 1 (∫ w, M * ‖g w‖), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun v => ?_⟩
  apply le_trans _ (le_max_right _ _)
  exact norm_integral_le_of_norm_le (hg.norm.const_mul M) (ae_of_all _ (fun w => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)))

def artinGammaPairLogJet (a b σ : ℝ) : ℕ → ℝ → ℂ :=
  artinConvolutionJet (artinGammaLogJet (a + σ))
    (artinMellinLogPullback (artinGammaDensity b) (σ : ℂ))

theorem artinGammaPairLogJet_zero (a b σ : ℝ) :
    artinGammaPairLogJet a b σ 0 =
      artinMellinLogPullback (artinGammaPairProfile a b) (σ : ℂ) := by
  funext v
  rw [artinGammaPairProfile, artinMellinLogPullback_convolution, convolution_mul_swap]
  unfold artinGammaPairLogJet artinConvolutionJet
  simp_rw [artinGammaLogJet, ← artinGammaDensity_log_weight a σ]

theorem artinGammaPairLogJet_hasDerivAt (a b σ : ℝ)
    (ha : 0 < a + σ) (hb : 0 < b + σ) (j : ℕ) (v : ℝ) :
    HasDerivAt (artinGammaPairLogJet a b σ j)
      (artinGammaPairLogJet a b σ (j + 1) v) v := by
  exact artinConvolutionJet_hasDerivAt (artinGammaLogJet_hasDerivAt · _ ·)
    (artinGammaLogJet_bound ha)
    ((artinMellin_convergent_iff_logPullback _ _).mp
      (artinGammaDensity_mellin_convergent b (by simpa using
        (show -b < σ by linarith)))) j v

theorem artinGammaPairLogJet_bound (a b σ : ℝ)
    (ha : 0 < a + σ) (hb : 0 < b + σ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ v, ‖artinGammaPairLogJet a b σ j v‖ ≤ M := by
  exact artinConvolutionJet_bound (artinGammaLogJet_bound ha)
    ((artinMellin_convergent_iff_logPullback _ _).mp
      (artinGammaDensity_mellin_convergent b (by simpa using
        (show -b < σ by linarith)))) j

theorem artinGammaPairProfile_log_smooth_bounded (a b σ : ℝ)
    (ha : 0 < a + σ) (hb : 0 < b + σ) :
    ContDiff ℝ ∞ (artinMellinLogPullback (artinGammaPairProfile a b) (σ : ℂ)) ∧
      ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ v,
        ‖iteratedDeriv j (artinMellinLogPullback (artinGammaPairProfile a b) (σ : ℂ)) v‖ ≤ M := by
  rw [← artinGammaPairLogJet_zero]
  have hd := artinGammaPairLogJet_hasDerivAt a b σ ha hb
  refine ⟨artinJetChain_contDiff hd, fun j => ?_⟩
  rw [artinJetChain_iteratedDeriv hd]
  exact artinGammaPairLogJet_bound a b σ ha hb j

end
end SimultaneousPrimitiveRoots
