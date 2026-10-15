module

public import SimultaneousPrimitiveRoots.GammaPairLogJets
public import SimultaneousPrimitiveRoots.BesselProfileBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology ContDiff
noncomputable section

theorem artinProfile_scale_log (f : ℝ → ℂ) (σ : ℝ) {A : ℝ} (hA : 0 < A)
    (D : ℂ) (v : ℝ) :
    artinMellinLogPullback (fun u => D * f (A * u)) (σ : ℂ) v =
      D * Complex.exp (-(σ : ℂ) * Real.log A) *
        artinMellinLogPullback f (σ : ℂ) (v - Real.log A) := by
  have he : Real.exp (-(v - Real.log A)) = A * Real.exp (-v) := by
    rw [show -(v - Real.log A) = Real.log A + -v by ring,
      Real.exp_add, Real.exp_log hA]
  unfold artinMellinLogPullback
  rw [he]
  have hex : Complex.exp (-(σ : ℂ) * Real.log A) *
      Complex.exp (-(σ : ℂ) * (v - Real.log A : ℝ)) =
      Complex.exp (-(σ : ℂ) * v) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = D * (Complex.exp (-(σ : ℂ) * Real.log A) *
        Complex.exp (-(σ : ℂ) * (v - Real.log A : ℝ))) * f (A * Real.exp (-v)) := by
      rw [hex]
      ring
    _ = _ := by ring

def artinBesselLogJet (c σ : ℝ) (j : ℕ) (v : ℝ) : ℂ :=
  ((2 / c ^ 2 : ℝ) : ℂ) * Complex.exp (-(σ : ℂ) * Real.log (c ^ 2 / 4)) *
    artinGammaPairLogJet (7 / 6) (5 / 6) σ j (v - Real.log (c ^ 2 / 4))

theorem artinBesselLogJet_zero {c : ℝ} (hc : 0 < c) (σ : ℝ) :
    artinBesselLogJet c σ 0 =
      artinMellinLogPullback (artinBesselLocalProfile c) (σ : ℂ) := by
  funext v
  rw [artinBesselLogJet, artinGammaPairLogJet_zero,
    ← artinProfile_scale_log _ σ (show 0 < c ^ 2 / 4 by positivity)]
  unfold artinMellinLogPullback
  rw [artinBesselLocalProfile_eq_gammaPair hc (Real.exp_pos _)]
  rfl

theorem artinBesselLogJet_hasDerivAt {c σ : ℝ} (_hc : 0 < c)
    (hσ : -(5 / 6 : ℝ) < σ) (j : ℕ) (v : ℝ) :
    HasDerivAt (artinBesselLogJet c σ j) (artinBesselLogJet c σ (j + 1) v) v := by
  simpa only [one_smul, Function.comp_apply, id_eq] using!
    ((artinGammaPairLogJet_hasDerivAt (7 / 6) (5 / 6) σ (by linarith) (by linarith)
      j (v - Real.log (c ^ 2 / 4))).scomp v
      ((hasDerivAt_id v).sub_const (Real.log (c ^ 2 / 4)))).const_mul
      (((2 / c ^ 2 : ℝ) : ℂ) * Complex.exp (-(σ : ℂ) * Real.log (c ^ 2 / 4)))

theorem artinBesselLogJet_bound {c σ : ℝ} (_hc : 0 < c)
    (hσ : -(5 / 6 : ℝ) < σ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ v, ‖artinBesselLogJet c σ j v‖ ≤ M := by
  obtain ⟨M, _, hM⟩ := artinGammaPairLogJet_bound (7 / 6) (5 / 6) σ
    (by linarith) (by linarith) j
  let D := ((2 / c ^ 2 : ℝ) : ℂ) * Complex.exp (-(σ : ℂ) * Real.log (c ^ 2 / 4))
  refine ⟨max 1 (‖D‖ * M), lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun v => ?_⟩
  apply le_trans _ (le_max_right _ _)
  rw [artinBesselLogJet, norm_mul]
  exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)

theorem artinBesselLocalProfile_log_smooth_bounded {c σ : ℝ} (hc : 0 < c)
    (hσ : -(5 / 6 : ℝ) < σ) :
    ContDiff ℝ ∞ (artinMellinLogPullback (artinBesselLocalProfile c) (σ : ℂ)) ∧
      ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ v,
        ‖iteratedDeriv j (artinMellinLogPullback (artinBesselLocalProfile c) (σ : ℂ)) v‖ ≤ M := by
  rw [← artinBesselLogJet_zero hc σ]
  have hd := artinBesselLogJet_hasDerivAt hc hσ
  refine ⟨artinJetChain_contDiff hd, fun j => ?_⟩
  rw [artinJetChain_iteratedDeriv hd]
  exact artinBesselLogJet_bound hc hσ j

theorem artinProfile_contDiffOn_of_log {f : ℝ → ℂ} {σ : ℝ}
    (hf : ContDiff ℝ ∞ (artinMellinLogPullback f (σ : ℂ))) :
    ContDiffOn ℝ ∞ f (Ioi 0) := by
  have hl : ContDiffOn ℝ ∞ (fun u : ℝ => -Real.log u) (Ioi 0) :=
    (Real.contDiffOn_log.mono (fun _ hu => ne_of_gt hu)).neg
  have h : ContDiffOn ℝ ∞ (fun u : ℝ =>
      Complex.exp (-(σ : ℂ) * Real.log u) *
        artinMellinLogPullback f (σ : ℂ) (-Real.log u)) (Ioi 0) := by
    apply ContDiffOn.mul
    · have hlc : ContDiffOn ℝ ∞ (fun u : ℝ => (Real.log u : ℂ)) (Ioi 0) :=
        Complex.ofRealCLM.contDiff.comp_contDiffOn
          (Real.contDiffOn_log.mono (fun _ hu => ne_of_gt hu))
      exact (contDiffOn_const.mul hlc).cexp
    · exact hf.contDiffOn.comp hl (mapsTo_univ _ _)
  exact h.congr (fun u hu => artinProfile_eq_weighted_log f σ hu)

theorem artinBesselLocalProfile_contDiffOn {c : ℝ} (hc : 0 < c) :
    ContDiffOn ℝ ∞ (artinBesselLocalProfile c) (Ioi 0) :=
  artinProfile_contDiffOn_of_log
    (artinBesselLocalProfile_log_smooth_bounded hc (σ := 0) (by norm_num)).1

end
end SimultaneousPrimitiveRoots
