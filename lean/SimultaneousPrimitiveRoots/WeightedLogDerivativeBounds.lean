module

public import SimultaneousPrimitiveRoots.BesselLogJets
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology ContDiff
noncomputable section

/-- The finite triangular combination implementing `(d/dv + sigma)^j`. -/
def artinJetLinearShift (σ : ℝ) (J : ℕ → ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0, v => J 0 v
  | j + 1, v => (σ : ℂ) * artinJetLinearShift σ J j v +
      artinJetLinearShift σ (fun k => J (k + 1)) j v

theorem artinJetLinearShift_hasDerivAt {J : ℕ → ℝ → ℂ}
    (hJ : ∀ j v, HasDerivAt (J j) (J (j + 1) v) v) (σ : ℝ) (j : ℕ) (v : ℝ) :
    HasDerivAt (artinJetLinearShift σ J j)
      (artinJetLinearShift σ (fun k => J (k + 1)) j v) v := by
  induction j generalizing J with
  | zero => exact hJ 0 v
  | succ j ih =>
    exact ((ih hJ).const_mul (σ : ℂ)).add (ih (fun k v => hJ (k + 1) v))

theorem artinJetLinearShift_bound {J : ℕ → ℝ → ℂ}
    (hb : ∀ j, ∃ M, 0 < M ∧ ∀ v, ‖J j v‖ ≤ M) (σ : ℝ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ v, ‖artinJetLinearShift σ J j v‖ ≤ M := by
  induction j generalizing J with
  | zero => exact hb 0
  | succ j ih =>
    obtain ⟨M, _, hM⟩ := ih hb
    obtain ⟨N, _, hB⟩ := ih (fun k => hb (k + 1))
    refine ⟨max 1 (‖(σ : ℂ)‖ * M + N), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
      fun v => ?_⟩
    apply le_trans _ (le_max_right _ _)
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hM v) (norm_nonneg _)) (hB v)

theorem artinUnweightedJet_hasDerivAt {J : ℕ → ℝ → ℂ}
    (hJ : ∀ j v, HasDerivAt (J j) (J (j + 1) v) v) (σ : ℝ) (j : ℕ) (v : ℝ) :
    HasDerivAt (fun w : ℝ => Complex.exp ((σ : ℂ) * w) * artinJetLinearShift σ J j w)
      (Complex.exp ((σ : ℂ) * v) * artinJetLinearShift σ J (j + 1) v) v := by
  have h := (((hasDerivAt_id v).ofReal_comp.const_mul (σ : ℂ)).cexp).mul
    (artinJetLinearShift_hasDerivAt hJ σ j v)
  simp only [id_eq, Complex.ofReal_one, mul_one] at h
  convert h using 1
  simp only [artinJetLinearShift]
  ring

/-- The actual negative-log derivative of the original profile. Its norm is
the norm of `(u d/du)^j f(u)`, since the sign is irrelevant to the bound. -/
def artinLogProfileJet (f : ℝ → ℂ) (j : ℕ) (u : ℝ) : ℂ :=
  iteratedDeriv j (fun v => f (Real.exp (-v))) (-Real.log u)

theorem artinLogProfileJet_zero (f : ℝ → ℂ) {u : ℝ} (hu : 0 < u) :
    artinLogProfileJet f 0 u = f u := by
  simp only [artinLogProfileJet, iteratedDeriv_zero, neg_neg, Real.exp_log hu]

theorem artinLogProfileJet_hasDerivAt {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ (fun v => f (Real.exp (-v)))) (j : ℕ) {u : ℝ}
    (hu : 0 < u) :
    HasDerivAt (artinLogProfileJet f j)
      ((-u⁻¹ : ℝ) • artinLogProfileJet f (j + 1) u) u := by
  have h := (hf.differentiable_iteratedDeriv j
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j) (-Real.log u)).hasDerivAt
  have hc := h.scomp u (Real.hasDerivAt_log hu.ne').neg
  simpa only [artinLogProfileJet, iteratedDeriv_succ, Function.comp_apply] using! hc

theorem artinLogProfileJet_negative_euler {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ (fun v => f (Real.exp (-v)))) (j : ℕ) {u : ℝ}
    (hu : 0 < u) :
    -(u : ℂ) * deriv (artinLogProfileJet f j) u = artinLogProfileJet f (j + 1) u := by
  rw [(artinLogProfileJet_hasDerivAt hf j hu).deriv, real_smul,
    Complex.ofReal_neg, Complex.ofReal_inv]
  have hn : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  field_simp

theorem artinLogProfileJet_bound_of_weighted {f : ℝ → ℂ} {σ : ℝ}
    (hf : ContDiff ℝ ∞ (artinMellinLogPullback f (σ : ℂ)))
    (hb : ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ v,
      ‖iteratedDeriv j (artinMellinLogPullback f (σ : ℂ)) v‖ ≤ M) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ u, 0 < u → ‖artinLogProfileJet f j u‖ ≤ M * u ^ (-σ) := by
  let J (k : ℕ) := iteratedDeriv k (artinMellinLogPullback f (σ : ℂ))
  have hJ : ∀ k v, HasDerivAt (J k) (J (k + 1) v) v := by
    intro k v
    dsimp only [J]
    rw [iteratedDeriv_succ]
    exact (hf.differentiable_iteratedDeriv k
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k) v).hasDerivAt
  have hzero : (fun v : ℝ => Complex.exp ((σ : ℂ) * v) * artinJetLinearShift σ J 0 v) =
      fun v => f (Real.exp (-v)) := by
    funext v
    simp only [artinJetLinearShift, J, iteratedDeriv_zero, artinMellinLogPullback,
      ← mul_assoc, ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero, one_mul]
  have hiter := artinJetChain_iteratedDeriv (artinUnweightedJet_hasDerivAt hJ σ) j
  rw [hzero] at hiter
  obtain ⟨M, hM, hB⟩ := artinJetLinearShift_bound hb σ j
  refine ⟨M, hM, fun u hu => ?_⟩
  rw [artinLogProfileJet, hiter, norm_mul, Complex.norm_exp]
  have he : ((σ : ℂ) * (-Real.log u : ℝ)).re = Real.log u * (-σ) := by simp; ring
  rw [he, ← Real.rpow_def_of_pos hu]
  exact (mul_le_mul_of_nonneg_left (hB _) (Real.rpow_nonneg hu.le _)).trans_eq
    (mul_comm _ _)

theorem artinBesselLocalProfile_logJet_power_bound {c σ : ℝ} (hc : 0 < c)
    (hσ : -(5 / 6 : ℝ) < σ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinBesselLocalProfile c) j u‖ ≤ M * u ^ (-σ) := by
  have h := artinBesselLocalProfile_log_smooth_bounded hc hσ
  exact artinLogProfileJet_bound_of_weighted h.1 h.2 j

end
end SimultaneousPrimitiveRoots
