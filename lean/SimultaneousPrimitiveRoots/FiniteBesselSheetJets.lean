module

public import SimultaneousPrimitiveRoots.BesselLogJets
public import SimultaneousPrimitiveRoots.FiniteBesselSheetBounds

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology ContDiff
noncomputable section

def artinFiniteSheetLogJet {n : ℕ} (f : Fin (n + 1) → ℝ → ℂ) (σ : ℝ)
    (J : ℕ → ℝ → ℂ) (j : ℕ) (v : ℝ) : ℂ :=
  ∫ x : Fin n → ℝ, J j (v + ∑ i, x i) *
    ∏ i : Fin n, artinMellinLogPullback (f i.succ) (σ : ℂ) (-x i)

theorem artinFiniteSheetLogJet_zero {n : ℕ} (f : Fin (n + 1) → ℝ → ℂ)
    (σ : ℝ) {J : ℕ → ℝ → ℂ}
    (hJ : J 0 = artinMellinLogPullback (f 0) (σ : ℂ)) :
    artinFiniteSheetLogJet f σ J 0 =
      artinMellinLogPullback (artinFinitePositiveNormSheetProfile n
        (fun p => ∏ i, f i (Real.exp (p i)))) (σ : ℂ) := by
  funext v
  have h := artinFiniteRadialProduct_weighted_sheet f σ (-v)
  have he : artinMellinLogPullback (artinFinitePositiveNormSheetProfile n
      (fun p => ∏ i, f i (Real.exp (p i)))) (σ : ℂ) v =
      ∫ x : Fin n → ℝ,
        artinMellinLogPullback (f 0) (σ : ℂ) (-(-v - ∑ i, x i)) *
          ∏ i : Fin n, artinMellinLogPullback (f i.succ) (σ : ℂ) (-x i) := by
    simpa only [artinMellinLogPullback, neg_mul, mul_neg, Complex.ofReal_neg] using h
  rw [he]
  unfold artinFiniteSheetLogJet
  rw [hJ]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    dsimp only
    rw [show -(-v - ∑ i, x i) = v + ∑ i, x i by ring])

theorem artinFiniteSheetLogJet_hasDerivAt {n : ℕ} {f : Fin (n + 1) → ℝ → ℂ}
    {σ : ℝ} {J : ℕ → ℝ → ℂ}
    (hJ : ∀ j v, HasDerivAt (J j) (J (j + 1) v) v)
    (hb : ∀ j, ∃ M, 0 < M ∧ ∀ v, ‖J j v‖ ≤ M)
    (hc : ∀ i : Fin n, Continuous (artinMellinLogPullback (f i.succ) (σ : ℂ)))
    (hi : ∀ i : Fin n, MellinConvergent (f i.succ) (σ : ℂ)) (j : ℕ) (v : ℝ) :
    HasDerivAt (artinFiniteSheetLogJet f σ J j)
      (artinFiniteSheetLogJet f σ J (j + 1) v) v := by
  have hJc (j : ℕ) : Continuous (J j) :=
    (show Differentiable ℝ (J j) from fun v => (hJ j v).differentiableAt).continuous
  unfold artinFiniteSheetLogJet
  apply artinIntegralJet_hasDerivAt (F := fun j v (x : Fin n → ℝ) => J j (v + ∑ i, x i) *
    ∏ i : Fin n, artinMellinLogPullback (f i.succ) (σ : ℂ) (-x i))
  · intro j v
    apply Continuous.aestronglyMeasurable
    exact ((hJc j).comp (by fun_prop)).mul
      (continuous_finsetProd _ (fun i _ => (hc i).comp (by fun_prop)))
  · intro j
    obtain ⟨M, _, hM⟩ := hb j
    refine ⟨fun x => M * ∏ i : Fin n,
      ‖artinMellinLogPullback (f i.succ) (σ : ℂ) (-x i)‖, ?_,
      ae_of_all _ (fun x v => ?_)⟩
    · exact (Integrable.fintype_prod (fun i =>
        (((artinMellin_convergent_iff_logPullback _ _).mp (hi i)).comp_neg).norm)).const_mul M
    · rw [norm_mul, norm_prod]
      exact mul_le_mul_of_nonneg_right (hM _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
  · intro j
    exact ae_of_all _ (fun x v => by
      simpa only [one_smul, Function.comp_apply, id_eq] using! ((hJ j (v + ∑ i, x i)).scomp v
        ((hasDerivAt_id v).add_const (∑ i, x i))).mul_const
        (∏ i : Fin n, artinMellinLogPullback (f i.succ) (σ : ℂ) (-x i)))

theorem artinFiniteSheetLogJet_bound {n : ℕ} {f : Fin (n + 1) → ℝ → ℂ}
    {σ : ℝ} {J : ℕ → ℝ → ℂ}
    (hb : ∀ j, ∃ M, 0 < M ∧ ∀ v, ‖J j v‖ ≤ M)
    (hi : ∀ i : Fin n, MellinConvergent (f i.succ) (σ : ℂ)) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ v, ‖artinFiniteSheetLogJet f σ J j v‖ ≤ M := by
  obtain ⟨M, _, hM⟩ := hb j
  let B (x : Fin n → ℝ) := M * ∏ i : Fin n,
    ‖artinMellinLogPullback (f i.succ) (σ : ℂ) (-x i)‖
  have hBi : Integrable B :=
    (Integrable.fintype_prod (fun i =>
      (((artinMellin_convergent_iff_logPullback _ _).mp (hi i)).comp_neg).norm)).const_mul M
  refine ⟨max 1 (∫ x, B x), lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun v => ?_⟩
  apply le_trans _ (le_max_right _ _)
  exact norm_integral_le_of_norm_le hBi (ae_of_all _ (fun x => by
    rw [norm_mul, norm_prod]
    exact mul_le_mul_of_nonneg_right (hM _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _))))

def artinFiniteBesselSheetLogJet {n : ℕ} (c : Fin (n + 1) → ℝ) (σ : ℝ) :
    ℕ → ℝ → ℂ :=
  artinFiniteSheetLogJet (fun i => artinBesselLocalProfile (c i)) σ
    (artinBesselLogJet (c 0) σ)

theorem artinFiniteBesselSheetLogJet_zero {n : ℕ} {c : Fin (n + 1) → ℝ}
    (hc : ∀ i, 0 < c i) (σ : ℝ) :
    artinFiniteBesselSheetLogJet c σ 0 =
      artinMellinLogPullback (artinFiniteBesselSheetProfile c) (σ : ℂ) :=
  artinFiniteSheetLogJet_zero _ σ (artinBesselLogJet_zero (hc 0) σ)

theorem artinFiniteBesselSheetLogJet_hasDerivAt {n : ℕ} {c : Fin (n + 1) → ℝ}
    (hc : ∀ i, 0 < c i) {σ : ℝ} (hσ : -(5 / 6 : ℝ) < σ) (j : ℕ) (v : ℝ) :
    HasDerivAt (artinFiniteBesselSheetLogJet c σ j)
      (artinFiniteBesselSheetLogJet c σ (j + 1) v) v :=
  artinFiniteSheetLogJet_hasDerivAt (artinBesselLogJet_hasDerivAt (hc 0) hσ)
    (artinBesselLogJet_bound (hc 0) hσ)
    (fun i => (artinBesselLocalProfile_log_regular (hc i.succ) hσ).1)
    (fun i => artinBesselLocalProfile_mellin_convergent (hc i.succ)
      (by simpa only [Complex.ofReal_re] using hσ)) j v

theorem artinFiniteBesselSheetLogJet_bound {n : ℕ} {c : Fin (n + 1) → ℝ}
    (hc : ∀ i, 0 < c i) {σ : ℝ} (hσ : -(5 / 6 : ℝ) < σ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ v, ‖artinFiniteBesselSheetLogJet c σ j v‖ ≤ M :=
  artinFiniteSheetLogJet_bound (artinBesselLogJet_bound (hc 0) hσ)
    (fun i => artinBesselLocalProfile_mellin_convergent (hc i.succ)
      (by simpa only [Complex.ofReal_re] using hσ)) j

theorem artinFiniteBesselSheetProfile_log_smooth_bounded {n : ℕ}
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {σ : ℝ}
    (hσ : -(5 / 6 : ℝ) < σ) :
    ContDiff ℝ ∞ (artinMellinLogPullback (artinFiniteBesselSheetProfile c) (σ : ℂ)) ∧
      ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ v,
        ‖iteratedDeriv j (artinMellinLogPullback (artinFiniteBesselSheetProfile c) (σ : ℂ)) v‖ ≤ M := by
  rw [← artinFiniteBesselSheetLogJet_zero hc σ]
  have hd := artinFiniteBesselSheetLogJet_hasDerivAt hc hσ
  refine ⟨artinJetChain_contDiff hd, fun j => ?_⟩
  rw [artinJetChain_iteratedDeriv hd]
  exact artinFiniteBesselSheetLogJet_bound hc hσ j

theorem artinFiniteBesselSheetProfile_contDiffOn {n : ℕ}
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) :
    ContDiffOn ℝ ∞ (artinFiniteBesselSheetProfile c) (Ioi 0) :=
  artinProfile_contDiffOn_of_log
    (artinFiniteBesselSheetProfile_log_smooth_bounded hc (σ := 0) (by norm_num)).1

end
end SimultaneousPrimitiveRoots
