module

public import SimultaneousPrimitiveRoots.FiniteBesselSheetJets
public import SimultaneousPrimitiveRoots.WeightedLogDerivativeBounds
public import SimultaneousPrimitiveRoots.NumberFieldBesselProfileBounds

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace SimultaneousPrimitiveRoots

open NumberField InfinitePlace MeasureTheory Set IsDedekindDomain
open scoped Topology ContDiff
noncomputable section

theorem artinProfile_const_mul_log_smooth_bounded {f : ℝ → ℂ} {σ : ℝ} (D : ℂ)
    (hf : ContDiff ℝ ∞ (artinMellinLogPullback f (σ : ℂ)))
    (hb : ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ v,
      ‖iteratedDeriv j (artinMellinLogPullback f (σ : ℂ)) v‖ ≤ M) :
    ContDiff ℝ ∞ (artinMellinLogPullback (fun u => D * f u) (σ : ℂ)) ∧
      ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ v,
        ‖iteratedDeriv j (artinMellinLogPullback (fun u => D * f u) (σ : ℂ)) v‖ ≤ M := by
  have he : artinMellinLogPullback (fun u => D * f u) (σ : ℂ) =
      fun v => D * artinMellinLogPullback f (σ : ℂ) v := by
    funext v
    unfold artinMellinLogPullback
    ring
  rw [he]
  refine ⟨contDiff_const.mul hf, fun j => ?_⟩
  obtain ⟨M, _, hM⟩ := hb j
  refine ⟨max 1 (‖D‖ * M), lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun v => ?_⟩
  rw [iteratedDeriv_const_mul_field, norm_mul]
  exact (mul_le_mul_of_nonneg_left (hM v) (norm_nonneg _)).trans (le_max_right _ _)

theorem artinFiniteBesselSheetProfile_logJet_power_bound {n : ℕ}
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {σ : ℝ}
    (hσ : -(5 / 6 : ℝ) < σ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinFiniteBesselSheetProfile c) j u‖ ≤ M * u ^ (-σ) := by
  have h := artinFiniteBesselSheetProfile_log_smooth_bounded hc hσ
  exact artinLogProfileJet_bound_of_weighted h.1 h.2 j

variable (K : Type*) [Field K] [NumberField K] (hr : 0 < nrComplexPlaces K)
  (μ : Measure (artinNumberFieldFiniteComplexNormKernel K)) [μ.IsHaarMeasure]
  (ν : Measure (ArtinNumberFieldFiniteUnits K)) [ν.IsHaarMeasure]
  {c : ArtinNumberFieldComplexPlaces K → ℝ} (hc : ∀ v, 0 < c v)

include μ ν hc

/-- All derivative orders of the actual full-kernel Haar profile have derived
weighted-log bounds. No derivative envelope on the fiber integral is an input. -/
theorem artinNumberFieldComplexCutoffBessel_log_smooth_bounded {σ : ℝ}
    (hσ : -(5 / 6 : ℝ) < σ) :
    ContDiff ℝ ∞ (artinMellinLogPullback
      (artinNumberFieldComplexCutoffBesselProfile K hr μ c) (σ : ℂ)) ∧
      ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ v,
        ‖iteratedDeriv j (artinMellinLogPullback
          (artinNumberFieldComplexCutoffBesselProfile K hr μ c) (σ : ℂ)) v‖ ≤ M := by
  rw [funext (artinNumberFieldComplexCutoffBesselProfile_model K hr μ c),
    funext (artinFiniteNormCutoffBesselProfile_factor _ _ _
      (artinNumberFieldFiniteLogNorm_cutoff K) _ ν
      (artinNumberFieldFiniteUnitCutoff_isCompact K)
      (artinNumberFieldFiniteUnitCutoff_isOpen K) _)]
  have h := artinFiniteBesselSheetProfile_log_smooth_bounded
    (fun i => hc (artinNumberFieldComplexPlaceIndex K hr i)) hσ
  exact artinProfile_const_mul_log_smooth_bounded _ h.1 h.2

theorem artinNumberFieldComplexCutoffBessel_contDiffOn :
    ContDiffOn ℝ ∞ (artinNumberFieldComplexCutoffBesselProfile K hr μ c) (Ioi 0) :=
  artinProfile_contDiffOn_of_log
    (artinNumberFieldComplexCutoffBessel_log_smooth_bounded K hr μ ν hc
      (σ := 0) (by norm_num)).1

theorem artinNumberFieldComplexCutoffBessel_logJet_power_bound {σ : ℝ}
    (hσ : -(5 / 6 : ℝ) < σ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinNumberFieldComplexCutoffBesselProfile K hr μ c) j u‖ ≤
        M * u ^ (-σ) := by
  have h := artinNumberFieldComplexCutoffBessel_log_smooth_bounded K hr μ ν hc hσ
  exact artinLogProfileJet_bound_of_weighted h.1 h.2 j

theorem artinNumberFieldComplexCutoffBessel_logJet_two_ended {α A : ℝ}
    (hα : α < 5 / 6) (hA : 0 < A) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinNumberFieldComplexCutoffBesselProfile K hr μ c) j u‖ ≤
        M * min (u ^ α) (u ^ (-A)) := by
  obtain ⟨M₁, hM₁, hb₁⟩ := artinNumberFieldComplexCutoffBessel_logJet_power_bound
    K hr μ ν hc (σ := -α) (by linarith) j
  obtain ⟨M₂, hM₂, hb₂⟩ := artinNumberFieldComplexCutoffBessel_logJet_power_bound
    K hr μ ν hc (σ := A) (by linarith) j
  refine ⟨max M₁ M₂, lt_of_lt_of_le hM₁ (le_max_left _ _), fun u hu => ?_⟩
  rw [mul_min_of_nonneg _ _ (le_of_lt (lt_of_lt_of_le hM₁ (le_max_left _ _)))]
  apply le_min
  · simpa only [neg_neg] using (hb₁ u hu).trans
      (mul_le_mul_of_nonneg_right (le_max_left M₁ M₂) (Real.rpow_nonneg hu.le (-(-α))))
  · exact (hb₂ u hu).trans
      (mul_le_mul_of_nonneg_right (le_max_right M₁ M₂) (Real.rpow_nonneg hu.le (-A)))

omit hc

theorem artinNumberFieldComplexCutoffBessel_logJet_family_bound
    {ι : Type*} [Fintype ι]
    (c : ι → ArtinNumberFieldComplexPlaces K → ℝ) (hc : ∀ i v, 0 < c i v)
    {σ : ℝ} (hσ : -(5 / 6 : ℝ) < σ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ i u, 0 < u →
      ‖artinLogProfileJet (artinNumberFieldComplexCutoffBesselProfile K hr μ (c i)) j u‖ ≤
        M * u ^ (-σ) := by
  classical
  have h (i : ι) := artinNumberFieldComplexCutoffBessel_logJet_power_bound K hr μ ν
    (hc i) hσ j
  choose M hM hb using h
  have hsum₀ : 0 ≤ ∑ i, M i := Finset.sum_nonneg (fun i _ => (hM i).le)
  refine ⟨1 + ∑ i, M i, by linarith, fun i u hu => ?_⟩
  have hle : M i ≤ 1 + ∑ k, M k := by
    have hsum := Finset.single_le_sum (s := Finset.univ)
      (fun k _ => (hM k).le) (Finset.mem_univ i)
    linarith
  exact (hb i u hu).trans (mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hu.le _))

end
end SimultaneousPrimitiveRoots
