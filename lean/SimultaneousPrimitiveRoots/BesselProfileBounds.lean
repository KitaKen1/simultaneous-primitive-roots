module

public import SimultaneousPrimitiveRoots.GammaProfileBounds
public import SimultaneousPrimitiveRoots.BesselKIntegralProfile

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology
noncomputable section

theorem artinProfile_scale_regular {f : ℝ → ℂ} {σ A : ℝ} (hA : 0 < A) (D : ℂ)
    (hc : ContinuousOn f (Ioi 0))
    (hb : ∃ M, 0 < M ∧ ∀ u, 0 < u → ‖f u‖ ≤ M * u ^ (-σ)) :
    ContinuousOn (fun u => D * f (A * u)) (Ioi 0) ∧
      ∃ M, 0 < M ∧ ∀ u, 0 < u → ‖D * f (A * u)‖ ≤ M * u ^ (-σ) := by
  constructor
  · exact continuousOn_const.mul (hc.comp (by fun_prop)
      (fun u hu => mul_pos hA hu))
  · obtain ⟨M, hM, hb⟩ := hb
    let B := ‖D‖ * M * A ^ (-σ)
    refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun u hu => ?_⟩
    calc
      _ ≤ ‖D‖ * (M * (A * u) ^ (-σ)) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hb _ (mul_pos hA hu)) (norm_nonneg _)
      _ = B * u ^ (-σ) := by rw [Real.mul_rpow hA.le hu.le]; ring
      _ ≤ max 1 B * u ^ (-σ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hu.le _)

theorem artinBesselLocalProfile_regular {c σ : ℝ} (hc : 0 < c)
    (hσ : -(5 / 6 : ℝ) < σ) :
    ContinuousOn (artinBesselLocalProfile c) (Ioi 0) ∧
      ∃ M, 0 < M ∧ ∀ u, 0 < u → ‖artinBesselLocalProfile c u‖ ≤ M * u ^ (-σ) := by
  have hg := artinGammaPairProfile_regular (7 / 6) (5 / 6) σ
    (by linarith) (by linarith)
  have hp := artinProfile_scale_regular (show 0 < c ^ 2 / 4 by positivity)
    ((2 / c ^ 2 : ℝ) : ℂ) hg.1 hg.2
  constructor
  · exact hp.1.congr (fun u hu => artinBesselLocalProfile_eq_gammaPair hc hu)
  · obtain ⟨M, hM, hb⟩ := hp.2
    refine ⟨M, hM, fun u hu => ?_⟩
    rw [artinBesselLocalProfile_eq_gammaPair hc hu]
    exact hb u hu

theorem artinProfile_log_regular_of_power {f : ℝ → ℂ} {σ : ℝ}
    (hc : ContinuousOn f (Ioi 0))
    (hb : ∃ M, 0 < M ∧ ∀ u, 0 < u → ‖f u‖ ≤ M * u ^ (-σ)) :
    Continuous (artinMellinLogPullback f (σ : ℂ)) ∧
      ∃ M, 0 < M ∧ ∀ v, ‖artinMellinLogPullback f (σ : ℂ) v‖ ≤ M := by
  constructor
  · exact (show Continuous (fun v : ℝ => Complex.exp (-(σ : ℂ) * v)) by
        fun_prop).mul (hc.comp_continuous (Real.continuous_exp.comp continuous_neg)
        (fun _ => Real.exp_pos _))
  · obtain ⟨M, hM, hb⟩ := hb
    refine ⟨M, hM, fun v => ?_⟩
    rw [artinMellinLogPullback, norm_mul, Complex.norm_exp]
    have he : (-(σ : ℂ) * v).re = -σ * v := by simp
    rw [he]
    calc
      _ ≤ Real.exp (-σ * v) * (M * (Real.exp (-v)) ^ (-σ)) :=
        mul_le_mul_of_nonneg_left (hb _ (Real.exp_pos _)) (Real.exp_pos _).le
      _ = M := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        rw [show -v * -σ = -(-σ * v) by ring, Real.exp_neg]
        have hn := Real.exp_ne_zero (-σ * v)
        field_simp

theorem artinBesselLocalProfile_log_regular {c σ : ℝ} (hc : 0 < c)
    (hσ : -(5 / 6 : ℝ) < σ) :
    Continuous (artinMellinLogPullback (artinBesselLocalProfile c) (σ : ℂ)) ∧
      ∃ M, 0 < M ∧ ∀ v,
        ‖artinMellinLogPullback (artinBesselLocalProfile c) (σ : ℂ) v‖ ≤ M := by
  have h := artinBesselLocalProfile_regular hc hσ
  exact artinProfile_log_regular_of_power h.1 h.2

end
end SimultaneousPrimitiveRoots
