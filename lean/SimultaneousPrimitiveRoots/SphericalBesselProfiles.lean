module

public import SimultaneousPrimitiveRoots.UniformProfilePowerBounds

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots
open Classical MeasureTheory Set Complex
open scoped Topology ContDiff BigOperators
noncomputable section

/-- A real radial weight applied to the original profile, before taking any transform. -/
def artinProfilePowerWeight (β : ℝ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  (u ^ β : ℝ) * f u

theorem artinProfilePowerWeight_eq_cpow (β : ℝ) (f : ℝ → ℂ) {u : ℝ}
    (hu : 0 < u) : artinProfilePowerWeight β f u = (u : ℂ) ^ (β : ℂ) * f u := by
  rw [artinProfilePowerWeight, ← Complex.ofReal_cpow hu.le]

theorem artinProfilePowerWeight_log (β : ℝ) (f : ℝ → ℂ) (s : ℂ) :
    artinMellinLogPullback (artinProfilePowerWeight β f) s =
      artinMellinLogPullback f (s + β) := by
  funext v
  rw [artinMellinLogPullback, artinProfilePowerWeight_eq_cpow β f (Real.exp_pos _),
    artinMellin_exp_power, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem artinProfilePowerWeight_iteratedDeriv (β : ℝ) (f : ℝ → ℂ)
    (σ : ℝ) (j : ℕ) (v : ℝ) :
    iteratedDeriv j (artinMellinLogPullback (artinProfilePowerWeight β f) (σ : ℂ)) v =
      iteratedDeriv j (artinMellinLogPullback f ((σ + β : ℝ) : ℂ)) v := by
  rw [artinProfilePowerWeight_log, Complex.ofReal_add]

theorem artinProfilePowerWeight_log_smooth (β : ℝ) {f : ℝ → ℂ} {σ : ℝ}
    (hf : ContDiff ℝ ∞ (artinMellinLogPullback f ((σ + β : ℝ) : ℂ))) :
    ContDiff ℝ ∞ (artinMellinLogPullback (artinProfilePowerWeight β f) (σ : ℂ)) := by
  simpa only [artinProfilePowerWeight_log, Complex.ofReal_add] using hf

theorem artinProfilePowerWeight_family_log_bounds {I : Type*} (β : ℝ)
    {f : I → ℝ → ℂ} {σ : ℝ}
    (hb : ∀ j, ∃ M, 0 < M ∧ ∀ i v,
      ‖iteratedDeriv j (artinMellinLogPullback (f i) ((σ + β : ℝ) : ℂ)) v‖ ≤ M) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ i v,
      ‖iteratedDeriv j (artinMellinLogPullback (artinProfilePowerWeight β (f i)) (σ : ℂ)) v‖ ≤ M := by
  simpa only [artinProfilePowerWeight_iteratedDeriv] using hb j

theorem artinProfilePowerWeight_family_power_bound {I : Type*} (β : ℝ)
    {f : I → ℝ → ℂ} {σ : ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (artinMellinLogPullback (f i) ((σ + β : ℝ) : ℂ)))
    (hb : ∀ j, ∃ M, 0 < M ∧ ∀ i v,
      ‖iteratedDeriv j (artinMellinLogPullback (f i) ((σ + β : ℝ) : ℂ)) v‖ ≤ M) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ i u, 0 < u →
      ‖artinLogProfileJet (artinProfilePowerWeight β (f i)) j u‖ ≤ M * u ^ (-σ) :=
  artinLogProfileJet_family_bound_of_weighted
    (fun i => artinProfilePowerWeight_log_smooth β (hf i))
    (fun k => artinProfilePowerWeight_family_log_bounds β hb k) j

theorem artinProfilePowerWeight_mellin_convergent (β : ℝ) (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent (artinProfilePowerWeight β f) s ↔ MellinConvergent f (s + β) := by
  rw [artinMellin_convergent_iff_logPullback,
    artinProfilePowerWeight_log, ← artinMellin_convergent_iff_logPullback]

theorem artinProfilePowerWeight_mellin (β : ℝ) (f : ℝ → ℂ) (s : ℂ) :
    mellin (artinProfilePowerWeight β f) s = mellin f (s + β) := by
  calc
    _ = mellin (fun u => (u : ℂ) ^ (β : ℂ) • f u) s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      change (u : ℂ) ^ (s - 1) * artinProfilePowerWeight β f u =
        (u : ℂ) ^ (s - 1) * ((u : ℂ) ^ (β : ℂ) * f u)
      rw [artinProfilePowerWeight_eq_cpow β f hu]
    _ = _ := mellin_cpow_smul f s (β : ℂ)

/-- The spherical radial K shape, defined from the actual convergent K integral.
Its identification with the original representation's Whittaker integral remains separate. -/
def artinSphericalBesselProfile (c u : ℝ) : ℂ :=
  (Real.sqrt u : ℂ) * artinBesselKIntegral (1 / 3) (c * Real.sqrt u)

theorem artinSphericalBesselProfile_eq_weight (c : ℝ) {u : ℝ} (hu : 0 < u) :
    artinSphericalBesselProfile c u =
      artinProfilePowerWeight (-(1 / 2)) (artinBesselLocalProfile c) u := by
  have hp : u ^ (-(1 / 2) : ℝ) * u = Real.sqrt u := by
    calc
      _ = u ^ (-(1 / 2) : ℝ) * u ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = u ^ ((-(1 / 2) : ℝ) + 1) := (Real.rpow_add hu _ _).symm
      _ = Real.sqrt u := by rw [Real.sqrt_eq_rpow]; norm_num
  unfold artinSphericalBesselProfile artinProfilePowerWeight artinBesselLocalProfile
  rw [← mul_assoc, ← Complex.ofReal_mul, hp]

theorem artinSphericalBesselProfile_eq_integral (c u : ℝ) :
    artinSphericalBesselProfile c u = (Real.sqrt u / 2 : ℝ) *
      ∫ t, artinBesselKIntegrand (1 / 3) (c * Real.sqrt u) t
        ∂artinPositiveMultiplicativeMeasure := by
  unfold artinSphericalBesselProfile artinBesselKIntegral
  push_cast
  ring

theorem artinSphericalBesselProfile_integrand_integrable {c u : ℝ}
    (hc : 0 < c) (hu : 0 < u) :
    Integrable (fun t => (Real.sqrt u / 2 : ℝ) *
      artinBesselKIntegrand (1 / 3) (c * Real.sqrt u) t)
      artinPositiveMultiplicativeMeasure :=
  (artinBesselKIntegrand_integrable (by norm_num)
    (mul_pos hc (Real.sqrt_pos.mpr hu))).const_mul _

theorem artinSphericalBesselProfile_log (c : ℝ) (s : ℂ) :
    artinMellinLogPullback (artinSphericalBesselProfile c) s =
      artinMellinLogPullback (artinBesselLocalProfile c) (s - 1 / 2) := by
  funext v
  rw [artinMellinLogPullback, artinSphericalBesselProfile_eq_weight c (Real.exp_pos _)]
  change artinMellinLogPullback (artinProfilePowerWeight (-(1 / 2))
    (artinBesselLocalProfile c)) s v = _
  have hshift : s + ((-(1 / 2) : ℝ) : ℂ) = s - 1 / 2 := by push_cast; ring
  rw [artinProfilePowerWeight_log, hshift]

theorem artinSphericalBesselProfile_log_smooth_bounded {c σ : ℝ} (hc : 0 < c)
    (hσ : -(1 / 3 : ℝ) < σ) :
    ContDiff ℝ ∞ (artinMellinLogPullback (artinSphericalBesselProfile c) (σ : ℂ)) ∧
      ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ v,
        ‖iteratedDeriv j (artinMellinLogPullback (artinSphericalBesselProfile c) (σ : ℂ)) v‖ ≤ M := by
  rw [artinSphericalBesselProfile_log]
  have h := artinBesselLocalProfile_log_smooth_bounded hc
    (σ := σ - 1 / 2) (by linarith)
  simpa only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using h

theorem artinSphericalBesselProfile_contDiffOn {c : ℝ} (hc : 0 < c) :
    ContDiffOn ℝ ∞ (artinSphericalBesselProfile c) (Ioi 0) :=
  artinProfile_contDiffOn_of_log
    (artinSphericalBesselProfile_log_smooth_bounded hc (σ := 0) (by norm_num)).1

theorem artinSphericalBesselProfile_logJet_power_bound {c σ : ℝ}
    (hc : 0 < c) (hσ : -(1 / 3 : ℝ) < σ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinSphericalBesselProfile c) j u‖ ≤ M * u ^ (-σ) := by
  have h := artinSphericalBesselProfile_log_smooth_bounded hc hσ
  exact artinLogProfileJet_bound_of_weighted h.1 h.2 j

theorem artinSphericalBesselProfile_logJet_two_ended {c α A : ℝ}
    (hc : 0 < c) (hα : α < 1 / 3) (hA : 0 < A) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinSphericalBesselProfile c) j u‖ ≤
        M * min (u ^ α) (u ^ (-A)) := by
  obtain ⟨M, hM, hbM⟩ := artinSphericalBesselProfile_logJet_power_bound
    hc (σ := -α) (by linarith) j
  obtain ⟨N, hN, hbN⟩ := artinSphericalBesselProfile_logJet_power_bound
    hc (σ := A) (by linarith) j
  refine ⟨max M N, lt_of_lt_of_le hM (le_max_left _ _), fun u hu => ?_⟩
  rw [mul_min_of_nonneg (u ^ α) (u ^ (-A))
    (le_of_lt (lt_of_lt_of_le hM (le_max_left _ _)))]
  apply le_min
  · simpa only [neg_neg] using (hbM u hu).trans
      (mul_le_mul_of_nonneg_right (le_max_left M N) (Real.rpow_nonneg hu.le _))
  · exact (hbN u hu).trans
      (mul_le_mul_of_nonneg_right (le_max_right M N) (Real.rpow_nonneg hu.le _))

theorem artinSphericalBesselProfile_mellin_convergent {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : -(1 / 3 : ℝ) < s.re) : MellinConvergent (artinSphericalBesselProfile c) s := by
  rw [artinMellin_convergent_iff_logPullback, artinSphericalBesselProfile_log,
    ← artinMellin_convergent_iff_logPullback]
  exact artinBesselLocalProfile_mellin_convergent hc (by
    norm_num [Complex.sub_re]; linarith)

theorem artinSphericalBesselProfile_mellin {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : -(1 / 3 : ℝ) < s.re) :
    mellin (artinSphericalBesselProfile c) s =
      ((2 / c ^ 2 : ℝ) : ℂ) * ((4 / c ^ 2 : ℝ) : ℂ) ^ (s - 1 / 2) *
        (Complex.Gamma (s + 1 / 3) * Complex.Gamma (s + 2 / 3)) := by
  have he : mellin (artinSphericalBesselProfile c) s =
      mellin (artinProfilePowerWeight (-(1 / 2)) (artinBesselLocalProfile c)) s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change (u : ℂ) ^ (s - 1) * artinSphericalBesselProfile c u =
      (u : ℂ) ^ (s - 1) *
        artinProfilePowerWeight (-(1 / 2)) (artinBesselLocalProfile c) u
    rw [artinSphericalBesselProfile_eq_weight c hu]
  rw [he, artinProfilePowerWeight_mellin]
  have hshift : s + ((-(1 / 2) : ℝ) : ℂ) = s - 1 / 2 := by push_cast; ring
  rw [hshift, artinBesselLocalProfile_mellin_gammaForm hc (by
    norm_num [Complex.sub_re]; linarith)]
  rw [show s - 1 / 2 + 5 / 6 = s + 1 / 3 by ring,
    show s - 1 / 2 + 7 / 6 = s + 2 / 3 by ring]

/-- An actual finite linear combination; the coefficients are independent of the radial variable. -/
def artinFiniteProfileCombination {I P : Type*} (s : Finset I) (a : P → I → ℂ)
    (f : I → ℝ → ℂ) (p : P) (u : ℝ) : ℂ := ∑ i ∈ s, a p i * f i u

theorem artinFiniteProfileCombination_log {I P : Type*} (s : Finset I)
    (a : P → I → ℂ) (f : I → ℝ → ℂ) (p : P) (σ : ℝ) :
    artinMellinLogPullback (artinFiniteProfileCombination s a f p) (σ : ℂ) =
      fun v => ∑ i ∈ s, a p i * artinMellinLogPullback (f i) (σ : ℂ) v := by
  funext v
  simp only [artinMellinLogPullback, artinFiniteProfileCombination, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem artinFiniteProfileCombination_log_smooth {I P : Type*} (s : Finset I)
    (a : P → I → ℂ) {f : I → ℝ → ℂ} {σ : ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (artinMellinLogPullback (f i) (σ : ℂ))) (p : P) :
    ContDiff ℝ ∞ (artinMellinLogPullback (artinFiniteProfileCombination s a f p) (σ : ℂ)) := by
  rw [artinFiniteProfileCombination_log]
  exact ContDiff.sum (fun i _ => contDiff_const.mul (hf i))

theorem artinFiniteProfileCombination_iteratedDeriv {I P : Type*} (s : Finset I)
    (a : P → I → ℂ) {f : I → ℝ → ℂ} {σ : ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (artinMellinLogPullback (f i) (σ : ℂ)))
    (p : P) (j : ℕ) (v : ℝ) :
    iteratedDeriv j (artinMellinLogPullback (artinFiniteProfileCombination s a f p) (σ : ℂ)) v =
      ∑ i ∈ s, a p i * iteratedDeriv j (artinMellinLogPullback (f i) (σ : ℂ)) v := by
  have hd : ∀ i ∈ s, ContDiffAt ℝ j
      (fun w => a p i * artinMellinLogPullback (f i) (σ : ℂ) w) v :=
    fun i _ => ((contDiff_const.mul (hf i)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).contDiffAt
  rw [artinFiniteProfileCombination_log, iteratedDeriv_fun_sum hd]
  simp only [iteratedDeriv_const_mul_field]

/-- Finite basis estimates yield one constant before every coefficient parameter.
The finite basis and the coefficient envelope are fixed. -/
theorem artinFiniteProfileCombination_uniform_log_bounds {I P : Type*}
    (s : Finset I) (a : P → I → ℂ) {f : I → ℝ → ℂ} {σ C : ℝ}
    (hC : 0 < C) (ha : ∀ p i, i ∈ s → ‖a p i‖ ≤ C)
    (hf : ∀ i, ContDiff ℝ ∞ (artinMellinLogPullback (f i) (σ : ℂ)))
    (hb : ∀ i j, ∃ M, 0 < M ∧ ∀ v,
      ‖iteratedDeriv j (artinMellinLogPullback (f i) (σ : ℂ)) v‖ ≤ M) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ p v,
      ‖iteratedDeriv j (artinMellinLogPullback (artinFiniteProfileCombination s a f p) (σ : ℂ)) v‖ ≤ M := by
  choose M _hM hbM using fun i => hb i j
  refine ⟨max 1 (C * ∑ i ∈ s, M i), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun p v => ?_⟩
  rw [artinFiniteProfileCombination_iteratedDeriv s a hf]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ s, C * M i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul (ha p i hi) (hbM i v) (norm_nonneg _) hC.le
    _ = C * ∑ i ∈ s, M i := (Finset.mul_sum ..).symm
    _ ≤ _ := le_max_right _ _

theorem artinFiniteProfileCombination_uniform_power_bound {I P : Type*}
    (s : Finset I) (a : P → I → ℂ) {f : I → ℝ → ℂ} {σ C : ℝ}
    (hC : 0 < C) (ha : ∀ p i, i ∈ s → ‖a p i‖ ≤ C)
    (hf : ∀ i, ContDiff ℝ ∞ (artinMellinLogPullback (f i) (σ : ℂ)))
    (hb : ∀ i j, ∃ M, 0 < M ∧ ∀ v,
      ‖iteratedDeriv j (artinMellinLogPullback (f i) (σ : ℂ)) v‖ ≤ M) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ p u, 0 < u →
      ‖artinLogProfileJet (artinFiniteProfileCombination s a f p) j u‖ ≤ M * u ^ (-σ) :=
  artinLogProfileJet_family_bound_of_weighted
    (artinFiniteProfileCombination_log_smooth s a hf)
    (artinFiniteProfileCombination_uniform_log_bounds s a hC ha hf hb) j

theorem artinFiniteProfileCombination_uniform_two_ended {I P : Type*}
    (s : Finset I) (a : P → I → ℂ) {f : I → ℝ → ℂ} {α A C : ℝ}
    (hC : 0 < C) (ha : ∀ p i, i ∈ s → ‖a p i‖ ≤ C)
    (hfα : ∀ i, ContDiff ℝ ∞ (artinMellinLogPullback (f i) ((-α : ℝ) : ℂ)))
    (hfA : ∀ i, ContDiff ℝ ∞ (artinMellinLogPullback (f i) (A : ℂ)))
    (hbα : ∀ i j, ∃ M, 0 < M ∧ ∀ v,
      ‖iteratedDeriv j (artinMellinLogPullback (f i) ((-α : ℝ) : ℂ)) v‖ ≤ M)
    (hbA : ∀ i j, ∃ M, 0 < M ∧ ∀ v,
      ‖iteratedDeriv j (artinMellinLogPullback (f i) (A : ℂ)) v‖ ≤ M) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ p u, 0 < u →
      ‖artinLogProfileJet (artinFiniteProfileCombination s a f p) j u‖ ≤
        M * min (u ^ α) (u ^ (-A)) := by
  obtain ⟨M, hM, hbM⟩ := artinFiniteProfileCombination_uniform_power_bound
    s a hC ha hfα hbα j
  obtain ⟨N, hN, hbN⟩ := artinFiniteProfileCombination_uniform_power_bound
    s a hC ha hfA hbA j
  refine ⟨max M N, lt_of_lt_of_le hM (le_max_left _ _), fun p u hu => ?_⟩
  rw [mul_min_of_nonneg (u ^ α) (u ^ (-A))
    (le_of_lt (lt_of_lt_of_le hM (le_max_left _ _)))]
  apply le_min
  · simpa only [neg_neg] using (hbM p u hu).trans
      (mul_le_mul_of_nonneg_right (le_max_left M N) (Real.rpow_nonneg hu.le _))
  · exact (hbN p u hu).trans
      (mul_le_mul_of_nonneg_right (le_max_right M N) (Real.rpow_nonneg hu.le _))

/-- The actual spherical K basis has common all-order two-ended estimates for
every family of bounded coefficients. This does not assert a representation-theoretic basis identity. -/
theorem artinSphericalBesselBasis_uniform_two_ended {I P : Type*}
    (s : Finset I) (a : P → I → ℂ) (c : I → ℝ) {α A C : ℝ}
    (hc : ∀ i, 0 < c i) (hα : α < 1 / 3) (hA : 0 < A)
    (hC : 0 < C) (ha : ∀ p i, i ∈ s → ‖a p i‖ ≤ C) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ p u, 0 < u →
      ‖artinLogProfileJet
        (artinFiniteProfileCombination s a (fun i => artinSphericalBesselProfile (c i)) p) j u‖ ≤
        M * min (u ^ α) (u ^ (-A)) := by
  have hleft := fun i => artinSphericalBesselProfile_log_smooth_bounded
    (hc i) (σ := -α) (by linarith)
  have hright := fun i => artinSphericalBesselProfile_log_smooth_bounded
    (hc i) (σ := A) (by linarith)
  exact artinFiniteProfileCombination_uniform_two_ended s a hC ha
    (fun i => (hleft i).1) (fun i => (hright i).1)
    (fun i => (hleft i).2) (fun i => (hright i).2) j

end
end SimultaneousPrimitiveRoots
