module

public import SimultaneousPrimitiveRoots.BesselProfileBounds
public import SimultaneousPrimitiveRoots.FiniteHaarBesselSheet

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology
noncomputable section

/-- Weighted sheet evaluation with its distinguished coordinate exposed. -/
theorem artinFiniteRadialProduct_weighted_sheet {n : ℕ}
    (f : Fin (n + 1) → ℝ → ℂ) (σ w : ℝ) :
    Complex.exp ((σ : ℂ) * w) * artinFinitePositiveNormSheetProfile n
      (fun p => ∏ i, f i (Real.exp (p i))) (Real.exp w) =
      ∫ x : Fin n → ℝ,
        artinMellinLogPullback (f 0) (σ : ℂ) (-(w - ∑ i, x i)) *
          ∏ i, artinMellinLogPullback (f i.succ) (σ : ℂ) (-x i) := by
  rw [artinFinitePositiveNormSheetProfile, Real.log_exp,
    ← artinFiniteLogNormSheet_weighted_profile]
  unfold artinFiniteLogNormSheetProfile
  simp_rw [artinFiniteRadialProduct_weighted, artinFiniteLogNormSheet_coordinates,
    Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    simp only [artinMellinLogPullback, Complex.ofReal_neg, neg_mul, mul_neg, neg_neg])

/-- One weighted supremum times the product of the other weighted L1 masses.
Continuity and the bound concern the actual finite-dimensional sheet integral. -/
theorem artinFiniteRadialProduct_log_regular {n : ℕ}
    {f : Fin (n + 1) → ℝ → ℂ} {σ : ℝ}
    (hc : ∀ i, Continuous (artinMellinLogPullback (f i) (σ : ℂ)))
    (hb : ∃ M, 0 < M ∧ ∀ v, ‖artinMellinLogPullback (f 0) (σ : ℂ) v‖ ≤ M)
    (hi : ∀ i : Fin n, MellinConvergent (f i.succ) (σ : ℂ)) :
    Continuous (artinMellinLogPullback (artinFinitePositiveNormSheetProfile n
      (fun p => ∏ i, f i (Real.exp (p i)))) (σ : ℂ)) ∧
      ∃ M, 0 < M ∧ ∀ v, ‖artinMellinLogPullback (artinFinitePositiveNormSheetProfile n
        (fun p => ∏ i, f i (Real.exp (p i)))) (σ : ℂ) v‖ ≤ M := by
  let F (w : ℝ) (x : Fin n → ℝ) : ℂ :=
    artinMellinLogPullback (f 0) (σ : ℂ) (-(w - ∑ i, x i)) *
      ∏ i : Fin n, artinMellinLogPullback (f i.succ) (σ : ℂ) (-x i)
  obtain ⟨M, hM, hb⟩ := hb
  let B (x : Fin n → ℝ) : ℝ := M *
    ∏ i : Fin n, ‖artinMellinLogPullback (f i.succ) (σ : ℂ) (-x i)‖
  have hBi : Integrable B := by
    exact (Integrable.fintype_prod (fun i =>
      (((artinMellin_convergent_iff_logPullback (f i.succ) (σ : ℂ)).mp
        (hi i)).comp_neg).norm)).const_mul M
  have hB (w : ℝ) : ∀ᵐ x, ‖F w x‖ ≤ B x := by
    exact ae_of_all _ (fun x => by
      dsimp only [F, B]
      rw [norm_mul, norm_prod]
      exact mul_le_mul_of_nonneg_right (hb _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  have hFc (w : ℝ) : Continuous (F w) := by
    unfold F
    apply Continuous.mul
    · exact (hc 0).comp (by fun_prop)
    · exact continuous_finsetProd _ (fun i _ => (hc i.succ).comp (by fun_prop))
  have hFw (x : Fin n → ℝ) : Continuous (fun w => F w x) := by
    exact ((hc 0).comp (by fun_prop)).mul continuous_const
  have hI : Continuous (fun w => ∫ x, F w x) :=
    continuous_of_dominated (fun w => (hFc w).aestronglyMeasurable) hB hBi
      (ae_of_all _ hFw)
  have he (v : ℝ) : artinMellinLogPullback (artinFinitePositiveNormSheetProfile n
      (fun p => ∏ i, f i (Real.exp (p i)))) (σ : ℂ) v = ∫ x, F (-v) x := by
    simpa only [artinMellinLogPullback, neg_mul, mul_neg, Complex.ofReal_neg, F] using
      artinFiniteRadialProduct_weighted_sheet f σ (-v)
  rw [funext he]
  refine ⟨hI.comp continuous_neg, max 1 (∫ x, B x),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun v => ?_⟩
  exact (norm_integral_le_of_norm_le hBi (hB (-v))).trans (le_max_right _ _)

theorem artinFiniteBesselSheetProfile_log_regular {n : ℕ}
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {σ : ℝ}
    (hσ : -(5 / 6 : ℝ) < σ) :
    Continuous (artinMellinLogPullback (artinFiniteBesselSheetProfile c) (σ : ℂ)) ∧
      ∃ M, 0 < M ∧ ∀ v,
        ‖artinMellinLogPullback (artinFiniteBesselSheetProfile c) (σ : ℂ) v‖ ≤ M := by
  exact artinFiniteRadialProduct_log_regular
    (fun i => (artinBesselLocalProfile_log_regular (hc i) hσ).1)
    (artinBesselLocalProfile_log_regular (hc 0) hσ).2
    (fun i => artinBesselLocalProfile_mellin_convergent (hc i.succ)
      (by simpa only [Complex.ofReal_re] using hσ))

theorem artinFiniteBesselSheetProfile_regular {n : ℕ}
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {σ : ℝ}
    (hσ : -(5 / 6 : ℝ) < σ) :
    ContinuousOn (artinFiniteBesselSheetProfile c) (Ioi 0) ∧
      ∃ M, 0 < M ∧ ∀ u, 0 < u → ‖artinFiniteBesselSheetProfile c u‖ ≤ M * u ^ (-σ) := by
  have h := artinFiniteBesselSheetProfile_log_regular hc hσ
  exact artinProfile_regular_of_log h.1 h.2

end
end SimultaneousPrimitiveRoots
