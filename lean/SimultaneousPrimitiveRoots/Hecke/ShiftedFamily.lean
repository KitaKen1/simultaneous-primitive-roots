module

public import SimultaneousPrimitiveRoots.Hecke.ShiftedTheta
public import SimultaneousPrimitiveRoots.Hecke.AveragedTheta

/-!
# Theta functions of shifted lattices and their averages as a `WeakFEPair`

For an invertible `A` of `ℝ^d` and a shift `v` with `m + v ≠ 0` for every `m ∈ ℤ^d`, put

`θ_{A,v}(t) = ∑_m exp(-π t |A(m + v)|²)`   and
`Φ_{A,v}(t) = ∑_n e(n·v) exp(-π t |A^{-T} n|²)`.

The shifted theta transformation (`tsum_shiftedGaussian_eq`) gives
`θ_{A,v}(1/x) = |det A|⁻¹ x^{d/2} Φ_{A,v}(x)` (`shiftedTheta_one_div`). Since the coset `ℤ^d + v`
avoids `0`, `θ_{A,v}` decays exponentially (`shiftedTheta_le_decay`), while `Φ_{A,v} - 1` does
too (`norm_phaseTheta_sub_one_le`).

Averaging over a `ThetaFamily` (constant covolume, uniform ellipticity) gives a weak FE-pair with
`f₀ = 0` and `g₀ = μ(P)` (`ThetaFamily.shiftedFEPair`). Its `Λ` is holomorphic on `ℂ \ {d/2}`:
there is no pole at `0`. For a number field it is the partial zeta function of a coset `α₀ + 𝔞`,
the input for the ray class partial zeta functions (step Z2 of `docs/unconditional-roadmap.md`).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open MeasureTheory Set Function Filter Complex Asymptotics
open scoped Real Topology

variable {d : Type*} [Fintype d]

/-! ### A positive distance from the shifted lattice to the origin -/

theorem abs_le_norm_intVec_add (m : d → ℤ) (v : d → ℝ) (i : d) :
    |(m i : ℝ) + v i| ≤ ‖intVec m + v‖ := by
  have := norm_le_pi_norm (intVec m + v) i
  simpa [intVec, Real.norm_eq_abs] using this

/-- The points of `ℤ^d + v` in a ball are finitely many. -/
theorem finite_shifted_ball (v : d → ℝ) (R : ℝ) :
    {m : d → ℤ | ‖intVec m + v‖ ≤ R}.Finite := by
  classical
  set N : ℕ := ⌈R + ‖v‖⌉₊ with hN
  refine (Set.Finite.pi (t := fun _ : d => (Set.Icc (-(N : ℤ)) N : Set ℤ))
    (fun _ => Set.finite_Icc _ _)).subset ?_
  intro m hm
  simp only [Set.mem_ofPred_eq] at hm
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_true_left]
  intro i
  have h1 := abs_le_norm_intVec_add m v i
  have hvi : |v i| ≤ ‖v‖ := by
    have := norm_le_pi_norm v i
    rwa [Real.norm_eq_abs] at this
  have h2 : |(m i : ℝ)| ≤ R + ‖v‖ := by
    have := abs_add_le ((m i : ℝ) + v i) (-v i)
    rw [add_neg_cancel_right, abs_neg] at this
    linarith
  have h3 : R + ‖v‖ ≤ (N : ℝ) := Nat.le_ceil _
  have h4 : |(m i : ℝ)| ≤ (N : ℝ) := h2.trans h3
  rw [abs_le] at h4
  constructor
  · exact_mod_cast h4.1
  · exact_mod_cast h4.2

/-- If the coset `ℤ^d + v` avoids `0`, its points stay a positive distance from `0`. -/
theorem exists_dist_shifted_pos (v : d → ℝ) (hv : ∀ m : d → ℤ, intVec m + v ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : d → ℤ, δ ≤ ‖intVec m + v‖ := by
  classical
  set S := (finite_shifted_ball (d := d) v 1).toFinset with hS
  by_cases hne : S.Nonempty
  · obtain ⟨m₀, -, hmin⟩ := S.exists_min_image (fun m => ‖intVec m + v‖) hne
    have hpos : 0 < ‖intVec m₀ + v‖ := norm_pos_iff.mpr (hv m₀)
    refine ⟨min ‖intVec m₀ + v‖ 1, lt_min hpos one_pos, fun m => ?_⟩
    by_cases hm : m ∈ S
    · exact (min_le_left _ _).trans (hmin m hm)
    · have : ¬ ‖intVec m + v‖ ≤ 1 := by
        intro h
        exact hm ((Set.Finite.mem_toFinset _).mpr h)
      exact (min_le_right _ _).trans (le_of_lt (not_le.mp this))
  · refine ⟨1, one_pos, fun m => ?_⟩
    by_contra h
    push Not at h
    exact hne ⟨m, (Set.Finite.mem_toFinset _).mpr h.le⟩

/-! ### The shifted theta function -/

/-- `θ_{A,v}(t) = ∑_m exp(-π t |A(m + v)|²)`. -/
def shiftedTheta (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (v : d → ℝ) (t : ℝ) : ℝ :=
  ∑' m : d → ℤ, Real.exp (-(π * t) * sqNorm (A (intVec m + v)))

/-- Domination of the shifted theta terms for `t ≥ t₀ ≥ 0`. -/
theorem exp_shifted_term_le (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {κ : ℝ}
    (hκA : ∀ u : d → ℝ, κ * ‖u‖ ^ 2 ≤ sqNorm (A u)) {t₀ t : ℝ} (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t)
    (v : d → ℝ) (m : d → ℤ) :
    Real.exp (-(π * t) * sqNorm (A (intVec m + v))) ≤
      Real.exp (-(π * t₀ * κ) * ‖intVec m + v‖ ^ 2) := by
  apply Real.exp_le_exp.mpr
  have h1 := hκA (intVec m + v)
  have h2 := sqNorm_nonneg (A (intVec m + v))
  have hp : 0 ≤ π * t₀ := by positivity
  have h3 : π * t₀ * (κ * ‖intVec m + v‖ ^ 2) ≤ π * t * sqNorm (A (intVec m + v)) := by
    calc π * t₀ * (κ * ‖intVec m + v‖ ^ 2) ≤ π * t₀ * sqNorm (A (intVec m + v)) :=
          mul_le_mul_of_nonneg_left h1 hp
      _ ≤ π * t * sqNorm (A (intVec m + v)) := by
          apply mul_le_mul_of_nonneg_right _ h2
          exact mul_le_mul_of_nonneg_left ht Real.pi_pos.le
  have e1 : -(π * t) * sqNorm (A (intVec m + v)) = -(π * t * sqNorm (A (intVec m + v))) := by
    ring
  have e2 : -(π * t₀ * κ) * ‖intVec m + v‖ ^ 2 = -(π * t₀ * (κ * ‖intVec m + v‖ ^ 2)) := by ring
  rw [e1, e2]
  linarith

/-- The shifted Gaussian majorant `∑_m exp(-a ‖m + v‖²)` is finite. -/
theorem summable_exp_neg_norm_sq_shift {a : ℝ} (ha : 0 < a) (v : d → ℝ) :
    Summable fun m : d → ℤ => Real.exp (-a * ‖intVec m + v‖ ^ 2) := by
  have hs := (summable_exp_neg_norm_sq (d := d) (a := a / 2) (by positivity)).mul_left
    (Real.exp (a * ‖v‖ ^ 2))
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun m => ?_) hs
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := half_norm_sq_sub_le v (intVec m)
  rw [add_comm v] at h
  nlinarith

theorem summable_shiftedTheta (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {t : ℝ} (ht : 0 < t) (v : d → ℝ) :
    Summable fun m : d → ℤ => Real.exp (-(π * t) * sqNorm (A (intVec m + v))) := by
  obtain ⟨κ, hκ, hκA⟩ := exists_sqNorm_lower A
  exact Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
    (exp_shifted_term_le A hκA ht.le le_rfl v)
    (summable_exp_neg_norm_sq_shift (by positivity) v)

theorem shiftedTheta_nonneg (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (v : d → ℝ) (t : ℝ) :
    0 ≤ shiftedTheta A v t :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

/-- Uniform upper bound for `t ≥ t₀ > 0` from an ellipticity constant. -/
theorem shiftedTheta_le_of_lower (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {κ t₀ t : ℝ} (hκ : 0 < κ)
    (hκA : ∀ u : d → ℝ, κ * ‖u‖ ^ 2 ≤ sqNorm (A u)) (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (v : d → ℝ) :
    shiftedTheta A v t ≤ ∑' m : d → ℤ, Real.exp (-(π * t₀ * κ) * ‖intVec m + v‖ ^ 2) :=
  Summable.tsum_le_tsum (fun m => exp_shifted_term_le A hκA ht₀.le ht v m)
    (summable_shiftedTheta A (by linarith) v)
    (summable_exp_neg_norm_sq_shift (by positivity) v)

/-- Exponential decay of `θ_{A,v}` when the coset `ℤ^d + v` stays at distance `≥ δ` from `0`. -/
theorem shiftedTheta_le_decay (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {κ : ℝ} (hκ : 0 < κ)
    (hκA : ∀ u : d → ℝ, κ * ‖u‖ ^ 2 ≤ sqNorm (A u)) {v : d → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hvδ : ∀ m : d → ℤ, δ ≤ ‖intVec m + v‖) {t : ℝ} (ht : 1 ≤ t) :
    shiftedTheta A v t ≤
      Real.exp (-(π * (κ * δ ^ 2)) * (t - 1)) *
        ∑' m : d → ℤ, Real.exp (-(π * κ) * ‖intVec m + v‖ ^ 2) := by
  have ht0 : 0 < t := by linarith
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (summable_shiftedTheta A ht0 v)
    ((summable_exp_neg_norm_sq_shift (by positivity) v).mul_left _)
  intro m
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hq : κ * ‖intVec m + v‖ ^ 2 ≤ sqNorm (A (intVec m + v)) := hκA (intVec m + v)
  have hδ2 : δ ^ 2 ≤ ‖intVec m + v‖ ^ 2 := pow_le_pow_left₀ hδ.le (hvδ m) 2
  have ht1 : 0 ≤ t - 1 := by linarith
  have hpk : 0 ≤ π * κ := by positivity
  -- `π t Q ≥ π κ ‖m+v‖² + π κ δ² (t - 1)`
  have e1 : π * κ * δ ^ 2 * (t - 1) ≤ π * κ * ‖intVec m + v‖ ^ 2 * (t - 1) := by
    apply mul_le_mul_of_nonneg_right _ ht1
    exact mul_le_mul_of_nonneg_left hδ2 hpk
  have e2 : π * κ * ‖intVec m + v‖ ^ 2 * t ≤ π * t * sqNorm (A (intVec m + v)) := by
    have := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ π * t)
    nlinarith
  nlinarith

theorem continuousOn_shiftedTheta (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (v : d → ℝ) :
    ContinuousOn (shiftedTheta A v) (Ioi 0) := by
  obtain ⟨κ, hκ, hκA⟩ := exists_sqNorm_lower A
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  have hx' : (0 : ℝ) < x / 2 := by positivity
  have hcont : ContinuousOn (fun t : ℝ => ∑' m : d → ℤ,
      Real.exp (-(π * t) * sqNorm (A (intVec m + v)))) (Ioi (x / 2)) := by
    refine continuousOn_tsum
      (u := fun m : d → ℤ => Real.exp (-(π * (x / 2) * κ) * ‖intVec m + v‖ ^ 2))
      (fun m => ?_) (summable_exp_neg_norm_sq_shift (by positivity) v) (fun m t ht => ?_)
    · exact (Continuous.continuousOn (by fun_prop))
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact exp_shifted_term_le A hκA hx'.le (le_of_lt ht) v m
  have hmem : Ioi (x / 2) ∈ 𝓝 x := Ioi_mem_nhds (by linarith)
  exact (hcont.continuousAt hmem).continuousWithinAt

/-- Continuity in the parameter of the shifted theta function of a uniformly elliptic family. -/
theorem continuous_shiftedTheta_of_lower {P : Type*} [TopologicalSpace P]
    {A : P → (d → ℝ) ≃ₗ[ℝ] (d → ℝ)} (hA : ∀ u, Continuous fun p => A p u) {κ : ℝ} (hκ : 0 < κ)
    (hlow : ∀ p u, κ * ‖u‖ ^ 2 ≤ sqNorm (A p u)) (v : d → ℝ) {t : ℝ} (ht : 0 < t) :
    Continuous fun p => shiftedTheta (A p) v t := by
  unfold shiftedTheta
  refine continuous_tsum (u := fun m : d → ℤ => Real.exp (-(π * t * κ) * ‖intVec m + v‖ ^ 2))
    (fun m => ?_) (summable_exp_neg_norm_sq_shift (by positivity) v) (fun m p => ?_)
  · have hs : Continuous (sqNorm (d := d)) := by
      unfold sqNorm
      fun_prop
    exact Real.continuous_exp.comp (continuous_const.mul (hs.comp (hA (intVec m + v))))
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact exp_shifted_term_le (A p) (hlow p) ht.le le_rfl v m

/-! ### The dual side: theta function with additive phases -/

variable [DecidableEq d]

/-- `Φ_{A,v}(t) = ∑_n e(n·v) exp(-π t |A^{-T} n|²)`. -/
def phaseTheta (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (v : d → ℝ) (t : ℝ) : ℂ :=
  ∑' n : d → ℤ, charPi n (-v) * ((Real.exp (-(π * t) * sqNorm (dualEquiv A (intVec n))) : ℝ) : ℂ)

omit [DecidableEq d] in
theorem charPi_zero_left (x : d → ℝ) : charPi (0 : d → ℤ) x = 1 := by
  simp only [charPi, neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply]

theorem norm_phaseTheta_term (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (v : d → ℝ) (t : ℝ) (n : d → ℤ) :
    ‖charPi n (-v) * ((Real.exp (-(π * t) * sqNorm (dualEquiv A (intVec n))) : ℝ) : ℂ)‖ =
      Real.exp (-(π * t) * sqNorm (dualEquiv A (intVec n))) := by
  rw [norm_mul, norm_charPi, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le]

theorem summable_phaseTheta (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (v : d → ℝ) {t : ℝ} (ht : 0 < t) :
    Summable fun n : d → ℤ =>
      charPi n (-v) * ((Real.exp (-(π * t) * sqNorm (dualEquiv A (intVec n))) : ℝ) : ℂ) := by
  refine Summable.of_norm ?_
  simp_rw [norm_phaseTheta_term]
  exact summable_theta (dualEquiv A) ht

theorem norm_phaseTheta_le (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (v : d → ℝ) {t : ℝ} (ht : 0 < t) :
    ‖phaseTheta A v t‖ ≤ latticeTheta (dualEquiv A) t :=
  tsum_of_norm_bounded (summable_theta (dualEquiv A) ht).hasSum
    fun n => (norm_phaseTheta_term A v t n).le

/-- `‖Φ_{A,v}(t) - 1‖ ≤ θ_{A^∨}(t) - 1`. -/
theorem norm_phaseTheta_sub_one_le' (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (v : d → ℝ) {t : ℝ}
    (ht : 0 < t) : ‖phaseTheta A v t - 1‖ ≤ latticeTheta (dualEquiv A) t - 1 := by
  set g : (d → ℤ) → ℝ := fun n => Real.exp (-(π * t) * sqNorm (dualEquiv A (intVec n))) with hg
  set c : (d → ℤ) → ℂ := fun n => charPi n (-v) * ((g n : ℝ) : ℂ) with hc
  have hgs : Summable g := summable_theta (dualEquiv A) ht
  have hcs : Summable c := summable_phaseTheta A v ht
  have hg0 : g 0 = 1 := by simp [hg, sqNorm_intVec_zero]
  have hc0 : c 0 = 1 := by simp [hc, hg0, charPi_zero_left]
  have h1 : phaseTheta A v t = 1 + ∑' n, ite (n = 0) 0 (c n) := by
    have := hcs.tsum_eq_add_tsum_ite (0 : d → ℤ)
    rw [hc0] at this
    exact this
  have h2 : latticeTheta (dualEquiv A) t = 1 + ∑' n, ite (n = 0) 0 (g n) := by
    have := hgs.tsum_eq_add_tsum_ite (0 : d → ℤ)
    rw [hg0] at this
    exact this
  have hsub : Summable fun n => ite (n = (0 : d → ℤ)) 0 (g n) :=
    hgs.of_nonneg_of_le (fun n => by split_ifs <;> simp [hg, (Real.exp_pos _).le])
      (fun n => by split_ifs <;> simp [hg, (Real.exp_pos _).le])
  rw [h1, h2, add_sub_cancel_left, add_sub_cancel_left]
  refine tsum_of_norm_bounded hsub.hasSum fun n => ?_
  split_ifs
  · simp
  · exact (norm_phaseTheta_term A v t n).le

/-- Exponential decay of `Φ_{A,v} - 1` with an explicit dual ellipticity constant. -/
theorem norm_phaseTheta_sub_one_le (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {κ : ℝ} (hκ : 0 < κ)
    (hκA : ∀ u : d → ℝ, κ * ‖u‖ ^ 2 ≤ sqNorm (dualEquiv A u)) (v : d → ℝ) {t : ℝ}
    (ht : 1 ≤ t) :
    ‖phaseTheta A v t - 1‖ ≤ Real.exp (-(π * κ) * (t - 1)) * gaussMajorant d (π * κ) :=
  (norm_phaseTheta_sub_one_le' A v (by linarith)).trans
    (latticeTheta_sub_one_le_of_lower (dualEquiv A) hκ hκA ht).2

theorem continuousOn_phaseTheta (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (v : d → ℝ) :
    ContinuousOn (phaseTheta A v) (Ioi 0) := by
  obtain ⟨κ, hκ, hκA⟩ := exists_sqNorm_lower (dualEquiv A)
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  have hx' : (0 : ℝ) < x / 2 := by positivity
  have hcont : ContinuousOn (fun t : ℝ => ∑' n : d → ℤ, charPi n (-v) *
      ((Real.exp (-(π * t) * sqNorm (dualEquiv A (intVec n))) : ℝ) : ℂ)) (Ioi (x / 2)) := by
    refine continuousOn_tsum
      (u := fun n : d → ℤ => Real.exp (-(π * (x / 2) * κ) * ‖intVec n‖ ^ 2))
      (fun n => ?_) (summable_exp_neg_norm_sq (by positivity)) (fun n t ht => ?_)
    · exact (Continuous.continuousOn (by fun_prop))
    · rw [norm_phaseTheta_term]
      exact exp_theta_term_le (dualEquiv A) hκA hx'.le (le_of_lt ht) n
  have hmem : Ioi (x / 2) ∈ 𝓝 x := Ioi_mem_nhds (by linarith)
  exact (hcont.continuousAt hmem).continuousWithinAt

/-- Continuity in the parameter of the dual theta function of a uniformly elliptic family. -/
theorem continuous_phaseTheta_of_lower {P : Type*} [TopologicalSpace P]
    {A : P → (d → ℝ) ≃ₗ[ℝ] (d → ℝ)} (hA : ∀ u, Continuous fun p => dualEquiv (A p) u) {κ : ℝ}
    (hκ : 0 < κ) (hlow : ∀ p u, κ * ‖u‖ ^ 2 ≤ sqNorm (dualEquiv (A p) u)) (v : d → ℝ) {t : ℝ}
    (ht : 0 < t) : Continuous fun p => phaseTheta (A p) v t := by
  unfold phaseTheta
  refine continuous_tsum (u := fun n : d → ℤ => Real.exp (-(π * t * κ) * ‖intVec n‖ ^ 2))
    (fun n => ?_) (summable_exp_neg_norm_sq (by positivity)) (fun n p => ?_)
  · have hs : Continuous (sqNorm (d := d)) := by
      unfold sqNorm
      fun_prop
    exact continuous_const.mul (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul (hs.comp (hA (intVec n))))))
  · rw [norm_phaseTheta_term]
    exact exp_theta_term_le (dualEquiv (A p)) (hlow p) ht.le le_rfl n

/-- The shifted theta transformation in the form required by `WeakFEPair`. -/
theorem shiftedTheta_one_div (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (v : d → ℝ) {x : ℝ} (hx : 0 < x) :
    ((shiftedTheta A v (1 / x) : ℝ) : ℂ) =
      ((|LinearMap.det (A : (d → ℝ) →ₗ[ℝ] (d → ℝ))|⁻¹ * x ^ ((Fintype.card d : ℝ) / 2) : ℝ)
        : ℂ) * phaseTheta A v x := by
  have h := tsum_shiftedGaussian_eq A (one_div_pos.mpr hx) v
  rw [one_div_one_div] at h
  unfold shiftedTheta phaseTheta
  rw [Complex.ofReal_tsum, h]
  congr 1
  apply tsum_congr
  intro n
  congr 3
  rw [div_eq_mul_inv, one_div, inv_inv]
  ring

/-- Big-O at `∞` from exponential decay, for complex-valued functions. -/
theorem isBigO_of_norm_sub_le {f : ℝ → ℂ} {c : ℂ} {M κ : ℝ} (hκ : 0 < κ)
    (h : ∀ t, 1 ≤ t → ‖f t - c‖ ≤ M * Real.exp (-(π * κ) * (t - 1))) (r : ℝ) :
    (fun t => f t - c) =O[atTop] (· ^ r) := by
  have h1 : (fun t => f t - c) =O[atTop] fun t => Real.exp (-(π * κ) * t) := by
    refine IsBigO.of_bound (|M| * Real.exp (π * κ)) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    have e : Real.exp (-(π * κ) * (t - 1)) = Real.exp (π * κ) * Real.exp (-(π * κ) * t) := by
      rw [← Real.exp_add]
      ring_nf
    have := h t ht
    rw [e] at this
    calc ‖f t - c‖ ≤ M * (Real.exp (π * κ) * Real.exp (-(π * κ) * t)) := this
      _ ≤ |M| * (Real.exp (π * κ) * Real.exp (-(π * κ) * t)) :=
          mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)
      _ = |M| * Real.exp (π * κ) * Real.exp (-(π * κ) * t) := by ring
  exact h1.trans (isLittleO_exp_neg_mul_rpow_atTop (by positivity) r).isBigO

/-! ### Averages over a family -/

namespace ThetaFamily

variable {P : Type*} [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
variable (F : ThetaFamily d P) (μ : Measure P) (v : d → ℝ)

/-- The averaged shifted theta function `∫ θ_{A_p,v}(t) dμ(p)`. -/
def shiftedAvg (t : ℝ) : ℝ := ∫ p, shiftedTheta (F.A p) v t ∂μ

/-- The averaged dual theta function with phases `∫ Φ_{A_p,v}(t) dμ(p)`. -/
def phaseAvg (t : ℝ) : ℂ := ∫ p, phaseTheta (F.A p) v t ∂μ

variable [IsFiniteMeasure μ]

theorem integrable_shiftedTheta {t : ℝ} (ht : 0 < t) :
    Integrable (fun p => shiftedTheta (F.A p) v t) μ := by
  refine Integrable.of_bound
    (continuous_shiftedTheta_of_lower F.continuous_A F.κ_pos F.lower v ht).aestronglyMeasurable
    (∑' m : d → ℤ, Real.exp (-(π * t * F.κ) * ‖intVec m + v‖ ^ 2)) (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (shiftedTheta_nonneg _ _ _)]
  exact shiftedTheta_le_of_lower (F.A p) F.κ_pos (F.lower p) ht le_rfl v

theorem integrable_phaseTheta {t : ℝ} (ht : 0 < t) :
    Integrable (fun p => phaseTheta (F.A p) v t) μ := by
  refine Integrable.of_bound (continuous_phaseTheta_of_lower F.continuous_dual F.κ_pos
    F.lower_dual v ht).aestronglyMeasurable (gaussMajorant d (π * t * F.κ))
    (ae_of_all _ fun p => ?_)
  exact (norm_phaseTheta_le _ v ht).trans
    (latticeTheta_le_of_lower (dualEquiv (F.A p)) F.κ_pos (F.lower_dual p) ht le_rfl)

theorem continuousOn_shiftedAvg : ContinuousOn (F.shiftedAvg μ v) (Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  have hx' : (0 : ℝ) < x / 2 := by positivity
  have hcont : ContinuousOn (fun t => ∫ p, shiftedTheta (F.A p) v t ∂μ) (Ioi (x / 2)) := by
    refine continuousOn_of_dominated
      (bound := fun _ => ∑' m : d → ℤ, Real.exp (-(π * (x / 2) * F.κ) * ‖intVec m + v‖ ^ 2))
      (fun t ht => ?_) (fun t ht => ae_of_all _ fun p => ?_) (integrable_const _)
      (ae_of_all _ fun p => ?_)
    · exact (continuous_shiftedTheta_of_lower F.continuous_A F.κ_pos F.lower v
        (lt_trans hx' ht)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (shiftedTheta_nonneg _ _ _)]
      exact shiftedTheta_le_of_lower (F.A p) F.κ_pos (F.lower p) hx' (le_of_lt ht) v
    · exact (continuousOn_shiftedTheta (F.A p) v).mono (Ioi_subset_Ioi hx'.le)
  have hmem : Ioi (x / 2) ∈ 𝓝 x := Ioi_mem_nhds (by linarith)
  exact (hcont.continuousAt hmem).continuousWithinAt

theorem continuousOn_phaseAvg : ContinuousOn (F.phaseAvg μ v) (Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  have hx' : (0 : ℝ) < x / 2 := by positivity
  have hcont : ContinuousOn (fun t => ∫ p, phaseTheta (F.A p) v t ∂μ) (Ioi (x / 2)) := by
    refine continuousOn_of_dominated (bound := fun _ => gaussMajorant d (π * (x / 2) * F.κ))
      (fun t ht => ?_) (fun t ht => ae_of_all _ fun p => ?_) (integrable_const _)
      (ae_of_all _ fun p => ?_)
    · exact (continuous_phaseTheta_of_lower F.continuous_dual F.κ_pos F.lower_dual v
        (lt_trans hx' ht)).aestronglyMeasurable
    · exact (norm_phaseTheta_le _ v (lt_trans hx' ht)).trans
        (latticeTheta_le_of_lower (dualEquiv (F.A p)) F.κ_pos (F.lower_dual p) hx'
          (le_of_lt ht))
    · exact (continuousOn_phaseTheta (F.A p) v).mono (Ioi_subset_Ioi hx'.le)
  have hmem : Ioi (x / 2) ∈ 𝓝 x := Ioi_mem_nhds (by linarith)
  exact (hcont.continuousAt hmem).continuousWithinAt

omit [OpensMeasurableSpace P] [IsFiniteMeasure μ] in
/-- **The averaged shifted theta transformation.** -/
theorem shiftedAvg_one_div {x : ℝ} (hx : 0 < x) :
    ((F.shiftedAvg μ v (1 / x) : ℝ) : ℂ) =
      ((F.covol⁻¹ * x ^ ((Fintype.card d : ℝ) / 2) : ℝ) : ℂ) * F.phaseAvg μ v x := by
  unfold shiftedAvg phaseAvg
  rw [← integral_complex_ofReal]
  have h : ∀ p, ((shiftedTheta (F.A p) v (1 / x) : ℝ) : ℂ) =
      ((F.covol⁻¹ * x ^ ((Fintype.card d : ℝ) / 2) : ℝ) : ℂ) * phaseTheta (F.A p) v x := by
    intro p
    rw [shiftedTheta_one_div (F.A p) v hx, F.abs_det p]
  simp_rw [h]
  rw [integral_const_mul]

omit [OpensMeasurableSpace P] in
/-- Exponential decay of the averaged shifted theta function. -/
theorem shiftedAvg_le {δ : ℝ} (hδ : 0 < δ) (hvδ : ∀ m : d → ℤ, δ ≤ ‖intVec m + v‖) {t : ℝ}
    (ht : 1 ≤ t) :
    |F.shiftedAvg μ v t| ≤ μ.real univ *
      (∑' m : d → ℤ, Real.exp (-(π * F.κ) * ‖intVec m + v‖ ^ 2)) *
        Real.exp (-(π * (F.κ * δ ^ 2)) * (t - 1)) := by
  rw [← Real.norm_eq_abs]
  have hb := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun p => shiftedTheta (F.A p) v t)
    (C := Real.exp (-(π * (F.κ * δ ^ 2)) * (t - 1)) *
      ∑' m : d → ℤ, Real.exp (-(π * F.κ) * ‖intVec m + v‖ ^ 2))
    (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (shiftedTheta_nonneg _ _ _)]
      exact shiftedTheta_le_decay (F.A p) F.κ_pos (F.lower p) hδ hvδ ht)
  unfold shiftedAvg
  linarith

/-- Exponential decay of the averaged dual theta function minus its constant term. -/
theorem norm_phaseAvg_sub_le {t : ℝ} (ht : 1 ≤ t) :
    ‖F.phaseAvg μ v t - ((μ.real univ : ℝ) : ℂ)‖ ≤
      μ.real univ * gaussMajorant d (π * F.κ) * Real.exp (-(π * F.κ) * (t - 1)) := by
  have ht0 : 0 < t := by linarith
  have heq : F.phaseAvg μ v t - ((μ.real univ : ℝ) : ℂ) =
      ∫ p, (phaseTheta (F.A p) v t - 1) ∂μ := by
    rw [integral_sub (F.integrable_phaseTheta μ v ht0) (integrable_const _), integral_const,
      Complex.real_smul, mul_one]
    rfl
  rw [heq]
  have hb := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun p => phaseTheta (F.A p) v t - 1)
    (C := Real.exp (-(π * F.κ) * (t - 1)) * gaussMajorant d (π * F.κ))
    (ae_of_all _ fun p => norm_phaseTheta_sub_one_le (F.A p) F.κ_pos (F.lower_dual p) v ht)
  linarith

/-- **The averaged theta functions of a coset avoiding `0` form a weak FE-pair** with `f₀ = 0`. -/
def shiftedFEPair [Nonempty d] (hv : ∀ m : d → ℤ, intVec m + v ≠ 0) : WeakFEPair ℂ where
  f := fun t => ((F.shiftedAvg μ v t : ℝ) : ℂ)
  g := F.phaseAvg μ v
  k := (Fintype.card d : ℝ) / 2
  ε := ((F.covol⁻¹ : ℝ) : ℂ)
  f₀ := 0
  g₀ := ((μ.real univ : ℝ) : ℂ)
  hf_int := (continuous_ofReal.comp_continuousOn
    (F.continuousOn_shiftedAvg μ v)).locallyIntegrableOn measurableSet_Ioi
  hg_int := (F.continuousOn_phaseAvg μ v).locallyIntegrableOn measurableSet_Ioi
  hk := by
    have h := Fintype.card_pos (α := d)
    have : (0 : ℝ) < Fintype.card d := by exact_mod_cast h
    positivity
  hε := by
    have : (0 : ℝ) < F.covol⁻¹ := inv_pos.mpr F.covol_pos
    exact_mod_cast this.ne'
  h_feq x hx := by
    simp only [smul_eq_mul]
    rw [F.shiftedAvg_one_div μ v hx]
    push_cast
    ring
  hf_top r := by
    obtain ⟨δ, hδ, hvδ⟩ := exists_dist_shifted_pos v hv
    have hκδ : 0 < F.κ * δ ^ 2 := by have := F.κ_pos; positivity
    exact isBigO_of_norm_sub_le (f := fun t => ((F.shiftedAvg μ v t : ℝ) : ℂ)) (c := 0) hκδ
      (M := μ.real univ * ∑' m : d → ℤ, Real.exp (-(π * F.κ) * ‖intVec m + v‖ ^ 2))
      (fun t ht => by
        rw [sub_zero, Complex.norm_real, Real.norm_eq_abs]
        exact F.shiftedAvg_le μ v hδ hvδ ht) r
  hg_top r := isBigO_of_norm_sub_le F.κ_pos
    (M := μ.real univ * gaussMajorant d (π * F.κ)) (fun t ht => F.norm_phaseAvg_sub_le μ v ht) r

variable [Nonempty d] (hv : ∀ m : d → ℤ, intVec m + v ≠ 0)

@[simp] theorem shiftedFEPair_k : (F.shiftedFEPair μ v hv).k = (Fintype.card d : ℝ) / 2 := rfl

@[simp] theorem shiftedFEPair_ε : (F.shiftedFEPair μ v hv).ε = ((F.covol⁻¹ : ℝ) : ℂ) := rfl

@[simp] theorem shiftedFEPair_f₀ : (F.shiftedFEPair μ v hv).f₀ = 0 := rfl

@[simp] theorem shiftedFEPair_g₀ :
    (F.shiftedFEPair μ v hv).g₀ = ((μ.real univ : ℝ) : ℂ) := rfl

/-- The `Λ` of a coset avoiding `0` is holomorphic away from `d/2`: no pole at `0`. -/
theorem shiftedFEPair_differentiableAt {s : ℂ} (hsk : s ≠ ((Fintype.card d : ℝ) / 2 : ℝ)) :
    DifferentiableAt ℂ (F.shiftedFEPair μ v hv).Λ s :=
  (F.shiftedFEPair μ v hv).differentiableAt_Λ (Or.inr rfl) (Or.inl hsk)

/-- The residue at `s = d/2` is `μ(P) / covol`, the same as for the full lattice. -/
theorem shiftedFEPair_residue :
    Tendsto (fun s : ℂ => (s - ((Fintype.card d : ℝ) / 2 : ℝ)) * (F.shiftedFEPair μ v hv).Λ s)
      (𝓝[≠] (((Fintype.card d : ℝ) / 2 : ℝ) : ℂ))
      (𝓝 (((F.covol⁻¹ : ℝ) : ℂ) * ((μ.real univ : ℝ) : ℂ))) := by
  have := (F.shiftedFEPair μ v hv).Λ_residue_k
  simpa [smul_eq_mul] using this

end ThetaFamily

end SimultaneousPrimitiveRoots.Hecke

end
