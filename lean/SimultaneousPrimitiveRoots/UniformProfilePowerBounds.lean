module

public import SimultaneousPrimitiveRoots.ReflectedClassUniformBounds

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots
open MeasureTheory Set Complex
open scoped Topology ContDiff
noncomputable section

/-- The finite triangular recurrence preserves uniformity in an arbitrary
parameter set; one constant is chosen before the parameter. -/
theorem artinJetLinearShift_family_bound {I : Type*} {J : I → ℕ → ℝ → ℂ}
    (hb : ∀ j, ∃ M, 0 < M ∧ ∀ i v, ‖J i j v‖ ≤ M) (σ : ℝ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ i v, ‖artinJetLinearShift σ (J i) j v‖ ≤ M := by
  induction j generalizing J with
  | zero => exact hb 0
  | succ j ih =>
    obtain ⟨M, _, hM⟩ := ih hb
    obtain ⟨N, _, hN⟩ := ih (J := fun i k => J i (k + 1)) (fun k => hb (k + 1))
    refine ⟨max 1 (‖(σ : ℂ)‖ * M + N), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
      fun i v => ?_⟩
    apply le_trans _ (le_max_right _ _)
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hM i v) (norm_nonneg _)) (hN i v)

theorem artinLogProfileJet_family_bound_of_weighted {I : Type*} {f : I → ℝ → ℂ} {σ : ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (artinMellinLogPullback (f i) (σ : ℂ)))
    (hb : ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ i v,
      ‖iteratedDeriv j (artinMellinLogPullback (f i) (σ : ℂ)) v‖ ≤ M) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ i u, 0 < u → ‖artinLogProfileJet (f i) j u‖ ≤ M * u ^ (-σ) := by
  let J (i : I) (k : ℕ) := iteratedDeriv k (artinMellinLogPullback (f i) (σ : ℂ))
  obtain ⟨M, hM, hB⟩ := artinJetLinearShift_family_bound (J := J) hb σ j
  refine ⟨M, hM, fun i u hu => ?_⟩
  have hJ : ∀ k v, HasDerivAt (J i k) (J i (k + 1) v) v := by
    intro k v
    dsimp only [J]
    rw [iteratedDeriv_succ]
    exact ((hf i).differentiable_iteratedDeriv k
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k) v).hasDerivAt
  have hzero : (fun v : ℝ => Complex.exp ((σ : ℂ) * v) * artinJetLinearShift σ (J i) 0 v) =
      fun v => f i (Real.exp (-v)) := by
    funext v
    simp only [artinJetLinearShift, J, iteratedDeriv_zero, artinMellinLogPullback,
      ← mul_assoc, ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero, one_mul]
  have hiter := artinJetChain_iteratedDeriv (artinUnweightedJet_hasDerivAt hJ σ) j
  rw [hzero] at hiter
  rw [artinLogProfileJet, hiter, norm_mul, Complex.norm_exp]
  have he : ((σ : ℂ) * (-Real.log u : ℝ)).re = Real.log u * (-σ) := by simp; ring
  rw [he, ← Real.rpow_def_of_pos hu]
  exact (mul_le_mul_of_nonneg_left (hB i _) (Real.rpow_nonneg hu.le _)).trans_eq
    (mul_comm _ _)

variable {G H X : Type*} [Monoid G] [Group H] [MeasurableSpace X] {μ : Measure X}

theorem artinReflectedClassBesselProfile_uniform_power_bound (n : ℕ) {k : ℕ}
    (hk : 0 < k) (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (B : Set H) (phase : H → H → Circle) (η : (Fin (n + 1) → Circle) → Circle)
    {c σ : ℝ} {τ : X → ℝ} {z : X → G × (Fin (n + 1) → ℂˣ)} {g : X → ℂ}
    (hc : 0 < c) (hσ : -(5 / 6 : ℝ) < σ) (hτ : Measurable τ)
    (hg : Integrable (artinShiftedBesselTail σ τ g) μ)
    (hB : ∀ κ, MeasurableSet {x | κ * (χ (z x))⁻¹ ∈ B})
    (hphase : ∀ κ, AEStronglyMeasurable (fun x => (phase κ (χ (z x)) : ℂ)) μ)
    (hη : AEStronglyMeasurable
      (fun x => (η (fun i => artinComplexUnitAngle ((z x).2 i)) : ℂ)) μ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ κ u, 0 < u →
      ‖artinLogProfileJet (artinReflectedClassBesselProfile μ n c χ B phase κ η τ z g) j u‖ ≤
        M * u ^ (-σ) :=
  artinLogProfileJet_family_bound_of_weighted
    (fun κ => (artinReflectedClassBesselProfile_log_smooth
      n hk χ he B phase κ η hc hσ hτ hg (hB κ) (hphase κ) hη).1)
    (fun j => artinReflectedClassBesselProfile_uniform_in_kappa
      n hk χ he B phase η hc hσ hτ hg hB hphase hη j) j

/-- All orders have a two-ended bound with a constant chosen before kappa.
The tail and its two weighted L1 norms, measure and local factor stay fixed. -/
theorem artinReflectedClassBesselProfile_uniform_two_ended (n : ℕ) {k : ℕ}
    (hk : 0 < k) (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (B : Set H) (phase : H → H → Circle) (η : (Fin (n + 1) → Circle) → Circle)
    {c α A : ℝ} {τ : X → ℝ} {z : X → G × (Fin (n + 1) → ℂˣ)} {g : X → ℂ}
    (hc : 0 < c) (hα : α < 5 / 6) (hA : 0 < A) (hτ : Measurable τ)
    (hgα : Integrable (artinShiftedBesselTail (-α) τ g) μ)
    (hgA : Integrable (artinShiftedBesselTail A τ g) μ)
    (hB : ∀ κ, MeasurableSet {x | κ * (χ (z x))⁻¹ ∈ B})
    (hphase : ∀ κ, AEStronglyMeasurable (fun x => (phase κ (χ (z x)) : ℂ)) μ)
    (hη : AEStronglyMeasurable
      (fun x => (η (fun i => artinComplexUnitAngle ((z x).2 i)) : ℂ)) μ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ κ u, 0 < u →
      ‖artinLogProfileJet (artinReflectedClassBesselProfile μ n c χ B phase κ η τ z g) j u‖ ≤
        M * min (u ^ α) (u ^ (-A)) := by
  obtain ⟨M, hM, hbM⟩ := artinReflectedClassBesselProfile_uniform_power_bound
    n hk χ he B phase η hc (σ := -α) (by linarith) hτ hgα hB hphase hη j
  obtain ⟨N, hN, hbN⟩ := artinReflectedClassBesselProfile_uniform_power_bound
    n hk χ he B phase η hc (σ := A) (by linarith) hτ hgA hB hphase hη j
  refine ⟨max M N, lt_of_lt_of_le hM (le_max_left _ _), fun κ u hu => ?_⟩
  rw [mul_min_of_nonneg (u ^ α) (u ^ (-A))
    (le_of_lt (lt_of_lt_of_le hM (le_max_left _ _)))]
  apply le_min
  · simpa only [neg_neg] using (hbM κ u hu).trans
      (mul_le_mul_of_nonneg_right (le_max_left M N) (Real.rpow_nonneg hu.le _))
  · exact (hbN κ u hu).trans
      (mul_le_mul_of_nonneg_right (le_max_right M N) (Real.rpow_nonneg hu.le _))

end
end SimultaneousPrimitiveRoots
