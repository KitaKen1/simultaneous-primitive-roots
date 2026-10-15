module

public import SimultaneousPrimitiveRoots.GammaPairProfile

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology Convolution
noncomputable section

/-- The elementary maximum of a positive Gamma density. -/
theorem artinGammaDensity_real_bound {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    t ^ p * Real.exp (-t) ≤ Real.exp (p * Real.log p - p) := by
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos ht hp)) hp.le
  rw [Real.log_div (ne_of_gt ht) (ne_of_gt hp)] at h
  have he : p * Real.log t - t ≤ p * Real.log p - p := by
    have hd : p * (t / p - 1) = t - p := by field_simp
    rw [hd] at h
    nlinarith
  rw [Real.rpow_def_of_pos ht, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by simpa only [sub_eq_add_neg, mul_comm] using he)

theorem artinGammaDensity_continuousOn (a : ℝ) :
    ContinuousOn (artinGammaDensity a) (Ioi 0) := by
  have hc : ContinuousOn (fun t : ℝ => ((t ^ a * Real.exp (-t) : ℝ) : ℂ))
      (Ioi 0) := by
    have hr : ContinuousOn (fun t : ℝ => t ^ a * Real.exp (-t)) (Ioi 0) :=
      (continuousOn_id.rpow_const
      (fun t ht => Or.inl (ne_of_gt ht))).mul
      (Real.continuous_exp.comp continuous_neg).continuousOn
    exact Complex.continuous_ofReal.comp_continuousOn hr
  exact hc.congr (fun t ht => artinGammaDensity_eq_ofReal a ht)

theorem artinGammaDensity_log_weight (a σ v : ℝ) :
    artinMellinLogPullback (artinGammaDensity a) (σ : ℂ) v =
      artinGammaDensity (a + σ) (Real.exp (-v)) := by
  rw [artinMellinLogPullback, ← artinMellin_exp_power,
    artinGammaDensity, artinGammaDensity, ← mul_assoc, ← Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))]
  congr 2
  push_cast
  ring

theorem artinGammaDensity_log_continuous (a σ : ℝ) :
    Continuous (artinMellinLogPullback (artinGammaDensity a) (σ : ℂ)) := by
  rw [funext (artinGammaDensity_log_weight a σ)]
  exact (artinGammaDensity_continuousOn (a + σ)).comp_continuous
    (Real.continuous_exp.comp continuous_neg) (fun v => Real.exp_pos _)

theorem artinGammaDensity_log_bound {a σ : ℝ} (ha : 0 < a + σ) (v : ℝ) :
    ‖artinMellinLogPullback (artinGammaDensity a) (σ : ℂ) v‖ ≤
      Real.exp ((a + σ) * Real.log (a + σ) - (a + σ)) := by
  rw [artinGammaDensity_log_weight, artinGammaDensity_eq_ofReal _ (Real.exp_pos _),
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact artinGammaDensity_real_bound ha (Real.exp_pos _)

/-- A bounded continuous factor and an L1 factor give a bounded continuous
weighted multiplicative convolution, at every point. -/
theorem artinMultiplicativeConvolution_log_regular {f g : ℝ → ℂ} {σ : ℝ}
    (hf : Continuous (artinMellinLogPullback f (σ : ℂ)))
    (hb : ∃ M, 0 < M ∧ ∀ v, ‖artinMellinLogPullback f (σ : ℂ) v‖ ≤ M)
    (hg : MellinConvergent g (σ : ℂ)) :
    Continuous (artinMellinLogPullback (artinMultiplicativeConvolution f g) (σ : ℂ)) ∧
      ∃ M, 0 < M ∧ ∀ v,
        ‖artinMellinLogPullback (artinMultiplicativeConvolution f g) (σ : ℂ) v‖ ≤ M := by
  obtain ⟨M, hM, hb⟩ := hb
  have hgb := (artinMellin_convergent_iff_logPullback g (σ : ℂ)).mp hg
  have hfb : BddAbove (range fun v => ‖artinMellinLogPullback f (σ : ℂ) v‖) := by
    exact ⟨M, by rintro _ ⟨v, rfl⟩; exact hb v⟩
  rw [funext (artinMellinLogPullback_convolution f g (σ : ℂ))]
  refine ⟨hfb.continuous_convolution_left_of_integrable
    (ContinuousLinearMap.mul ℂ ℂ) hf hgb, ?_⟩
  let B := M * ∫ v, ‖artinMellinLogPullback g (σ : ℂ) v‖
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun v => ?_⟩
  rw [convolution_mul_swap]
  apply le_trans _ (le_max_right _ _)
  change ‖∫ w, artinMellinLogPullback f (σ : ℂ) (v - w) *
    artinMellinLogPullback g (σ : ℂ) w‖ ≤ B
  calc
    _ ≤ ∫ w, M * ‖artinMellinLogPullback g (σ : ℂ) w‖ := by
      apply norm_integral_le_of_norm_le (hgb.norm.const_mul M)
      exact ae_of_all _ (fun w => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hb (v - w)) (norm_nonneg _))
    _ = B := integral_const_mul _ _

theorem artinGammaPairProfile_log_regular (a b σ : ℝ)
    (ha : 0 < a + σ) (hb : 0 < b + σ) :
    Continuous (artinMellinLogPullback (artinGammaPairProfile a b) (σ : ℂ)) ∧
      ∃ M, 0 < M ∧ ∀ v,
        ‖artinMellinLogPullback (artinGammaPairProfile a b) (σ : ℂ) v‖ ≤ M := by
  exact artinMultiplicativeConvolution_log_regular
    (artinGammaDensity_log_continuous a σ)
    ⟨_, Real.exp_pos _, artinGammaDensity_log_bound ha⟩
    (artinGammaDensity_mellin_convergent b (by simpa using (show -b < σ by linarith)))

theorem artinProfile_eq_weighted_log (f : ℝ → ℂ) (σ : ℝ) {u : ℝ} (hu : 0 < u) :
    f u = Complex.exp (-(σ : ℂ) * Real.log u) *
      artinMellinLogPullback f (σ : ℂ) (-Real.log u) := by
  simp only [artinMellinLogPullback, neg_neg, Real.exp_log hu]
  rw [← mul_assoc, ← Complex.exp_add]
  have he : -(σ : ℂ) * Real.log u + -(σ : ℂ) * (-Real.log u : ℝ) = 0 := by
    push_cast; ring
  rw [he, Complex.exp_zero, one_mul]

/-- A weighted log bound supplies both positive-axis continuity and the
global power bound needed by the actual ideal-series Fubini theorem. -/
theorem artinProfile_regular_of_log {f : ℝ → ℂ} {σ : ℝ}
    (hc : Continuous (artinMellinLogPullback f (σ : ℂ)))
    (hb : ∃ M, 0 < M ∧ ∀ v, ‖artinMellinLogPullback f (σ : ℂ) v‖ ≤ M) :
    ContinuousOn f (Ioi 0) ∧ ∃ M, 0 < M ∧ ∀ u, 0 < u → ‖f u‖ ≤ M * u ^ (-σ) := by
  constructor
  · have hl : ContinuousOn (fun u : ℝ => -Real.log u) (Ioi 0) :=
      (Real.continuousOn_log.mono (fun _ hu => ne_of_gt hu)).neg
    have h := (show ContinuousOn (fun u : ℝ =>
        Complex.exp (-(σ : ℂ) * Real.log u)) (Ioi 0) by
      fun_prop (disch := aesop)).mul (hc.continuousOn.comp hl (mapsTo_univ _ _))
    exact h.congr (fun u hu => artinProfile_eq_weighted_log f σ hu)
  · obtain ⟨M, hM, hb⟩ := hb
    refine ⟨M, hM, fun u hu => ?_⟩
    rw [artinProfile_eq_weighted_log f σ hu, norm_mul, Complex.norm_exp]
    have he : (-(σ : ℂ) * Real.log u).re = Real.log u * (-σ) := by simp; ring
    rw [he, ← Real.rpow_def_of_pos hu]
    exact (mul_le_mul_of_nonneg_left (hb _) (Real.rpow_nonneg hu.le _)).trans_eq
      (mul_comm _ _)

theorem artinGammaPairProfile_regular (a b σ : ℝ)
    (ha : 0 < a + σ) (hb : 0 < b + σ) :
    ContinuousOn (artinGammaPairProfile a b) (Ioi 0) ∧
      ∃ M, 0 < M ∧ ∀ u, 0 < u → ‖artinGammaPairProfile a b u‖ ≤ M * u ^ (-σ) := by
  have h := artinGammaPairProfile_log_regular a b σ ha hb
  exact artinProfile_regular_of_log h.1 h.2

end
end SimultaneousPrimitiveRoots
