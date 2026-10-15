module

public import SimultaneousPrimitiveRoots.Hecke.EpsteinZeta

/-!
# Averaged lattice theta functions as a `WeakFEPair`

Let `p ↦ A_p` be a continuous family of lattices `A_p ℤ^d` with constant covolume and a uniform
ellipticity bound, parametrized by a finite measure space `(P, μ)`. Averaging the theta
transformation of D2 over `P` gives a functional equation for

`F(t) = ∫_P θ_{A_p}(t) dμ(p)`   and   `F^∨(t) = ∫_P θ_{A_p^∨}(t) dμ(p)`,

so `(F, F^∨)` is a weak FE-pair with `k = d/2`, `ε = covol⁻¹` and constant terms `μ(P)`.

This is Hecke's construction: for a number field, `P` is a fundamental domain of the units in the
norm-one torus of weights, and the Mellin transform of `F - μ(P)` is a partial Dedekind zeta
function (step D3d/D3e of `docs/b7-dedekind-blueprint.md`).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open MeasureTheory Set Function Filter Complex Asymptotics
open scoped Real Topology

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The Gaussian majorant `S(a) = ∑_m exp(-a ‖m‖²)`. -/
def gaussMajorant (d : Type*) [Fintype d] (a : ℝ) : ℝ :=
  ∑' m : d → ℤ, Real.exp (-a * ‖intVec m‖ ^ 2)

omit [DecidableEq d] in
theorem latticeTheta_nonneg (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (t : ℝ) : 0 ≤ latticeTheta A t :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

/-- Uniform upper bound for `t ≥ t₀ > 0` from an ellipticity constant. -/
theorem latticeTheta_le_of_lower (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {κ t₀ t : ℝ} (hκ : 0 < κ)
    (hκA : ∀ v : d → ℝ, κ * ‖v‖ ^ 2 ≤ sqNorm (A v)) (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    latticeTheta A t ≤ gaussMajorant d (π * t₀ * κ) :=
  Summable.tsum_le_tsum (fun m => exp_theta_term_le A hκA ht₀.le ht m)
    (summable_theta A (by linarith)) (summable_exp_neg_norm_sq (by positivity))

/-- Exponential decay of `θ_A(t) - 1` with an explicit ellipticity constant. -/
theorem latticeTheta_sub_one_le_of_lower (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {κ : ℝ} (hκ : 0 < κ)
    (hκA : ∀ v : d → ℝ, κ * ‖v‖ ^ 2 ≤ sqNorm (A v)) {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ latticeTheta A t - 1 ∧
      latticeTheta A t - 1 ≤ Real.exp (-(π * κ) * (t - 1)) * gaussMajorant d (π * κ) := by
  classical
  have ht0 : 0 < t := by linarith
  set g : ℝ → (d → ℤ) → ℝ := fun t m => Real.exp (-(π * t) * sqNorm (A (intVec m))) with hg
  have hsum_t : Summable (g t) := summable_theta A ht0
  have hsum_1 : Summable (g 1) := summable_theta A one_pos
  have hsplit : ∀ u, Summable (g u) → latticeTheta A u = 1 + ∑' m, ite (m = 0) 0 (g u m) := by
    intro u hu
    have := hu.tsum_eq_add_tsum_ite (0 : d → ℤ)
    have hg0 : g u 0 = 1 := by simp [hg, sqNorm_intVec_zero]
    rw [hg0] at this
    exact this
  rw [hsplit t hsum_t]
  have hsub_t : Summable fun m => ite (m = (0 : d → ℤ)) 0 (g t m) :=
    hsum_t.of_nonneg_of_le (fun m => by split_ifs <;> simp [hg, (Real.exp_pos _).le])
      (fun m => by split_ifs <;> simp [hg, (Real.exp_pos _).le])
  have hsub_1 : Summable fun m => ite (m = (0 : d → ℤ)) 0 (g 1 m) :=
    hsum_1.of_nonneg_of_le (fun m => by split_ifs <;> simp [hg, (Real.exp_pos _).le])
      (fun m => by split_ifs <;> simp [hg, (Real.exp_pos _).le])
  refine ⟨by
    simp only [add_sub_cancel_left]
    exact tsum_nonneg fun m => by split_ifs <;> simp [hg, (Real.exp_pos _).le], ?_⟩
  simp only [add_sub_cancel_left]
  have hterm : ∀ m : d → ℤ, ite (m = 0) 0 (g t m) ≤
      Real.exp (-(π * κ) * (t - 1)) * ite (m = 0) 0 (g 1 m) := by
    intro m
    split_ifs with hm
    · simp
    · simp only [hg]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 := one_le_norm_intVec hm
      have h2 : 1 ≤ ‖intVec m‖ ^ 2 := by nlinarith
      have h3 := hκA (intVec m)
      have hs : κ ≤ sqNorm (A (intVec m)) := by nlinarith
      have ht1 : 0 ≤ t - 1 := by linarith
      have : π * κ * (t - 1) ≤ π * (t - 1) * sqNorm (A (intVec m)) := by
        have := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ π * (t - 1))
        linarith
      nlinarith
  have hle := Summable.tsum_le_tsum hterm hsub_t (hsub_1.mul_left _)
  rw [tsum_mul_left] at hle
  refine hle.trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have h1 : ∑' m, ite (m = (0 : d → ℤ)) 0 (g 1 m) ≤ latticeTheta A 1 := by
    rw [hsplit 1 hsum_1]
    linarith
  have h2 : latticeTheta A 1 ≤ gaussMajorant d (π * 1 * κ) :=
    latticeTheta_le_of_lower A hκ hκA one_pos le_rfl
  rw [mul_one] at h2
  linarith

/-- Small-`t` bound from the theta transformation and the dual ellipticity constant. -/
theorem latticeTheta_le_small (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {κ : ℝ} (hκ : 0 < κ)
    (hκA : ∀ v : d → ℝ, κ * ‖v‖ ^ 2 ≤ sqNorm (dualEquiv A v)) {t : ℝ} (ht : 0 < t)
    (ht1 : t ≤ 1) :
    latticeTheta A t ≤ |LinearMap.det (A : (d → ℝ) →ₗ[ℝ] (d → ℝ))|⁻¹ *
      t ^ (-((Fintype.card d : ℝ) / 2)) * gaussMajorant d (π * κ) := by
  have hx : 0 < 1 / t := by positivity
  have h := latticeTheta_one_div A hx
  rw [one_div_one_div] at h
  rw [h]
  have hdual : latticeTheta (dualEquiv A) (1 / t) ≤ gaussMajorant d (π * 1 * κ) :=
    latticeTheta_le_of_lower (dualEquiv A) hκ hκA one_pos (by rw [le_div_iff₀ ht]; linarith)
  rw [mul_one] at hdual
  have hpow : (1 / t) ^ ((Fintype.card d : ℝ) / 2) = t ^ (-((Fintype.card d : ℝ) / 2)) := by
    rw [Real.rpow_neg ht.le, one_div, Real.inv_rpow ht.le]
  rw [hpow]
  have hdet : 0 ≤ |LinearMap.det (A : (d → ℝ) →ₗ[ℝ] (d → ℝ))|⁻¹ := by positivity
  have hp : 0 ≤ t ^ (-((Fintype.card d : ℝ) / 2)) := Real.rpow_nonneg ht.le _
  exact mul_le_mul_of_nonneg_left hdual (mul_nonneg hdet hp)

/-- A continuous family of lattices with constant covolume and uniform ellipticity. -/
structure ThetaFamily (d P : Type*) [Fintype d] [DecidableEq d] [TopologicalSpace P] where
  /-- The lattices `A_p ℤ^d`. -/
  A : P → (d → ℝ) ≃ₗ[ℝ] (d → ℝ)
  continuous_A : ∀ v, Continuous fun p => A p v
  continuous_dual : ∀ v, Continuous fun p => dualEquiv (A p) v
  /-- A uniform ellipticity constant for the family and its dual. -/
  κ : ℝ
  κ_pos : 0 < κ
  lower : ∀ p v, κ * ‖v‖ ^ 2 ≤ sqNorm (A p v)
  lower_dual : ∀ p v, κ * ‖v‖ ^ 2 ≤ sqNorm (dualEquiv (A p) v)
  /-- The common covolume `|det A_p|`. -/
  covol : ℝ
  covol_pos : 0 < covol
  abs_det : ∀ p, |LinearMap.det (A p : (d → ℝ) →ₗ[ℝ] (d → ℝ))| = covol

namespace ThetaFamily

variable {P : Type*} [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
variable (F : ThetaFamily d P) (μ : Measure P)

/-- Continuity in the parameter of the theta function of a uniformly elliptic family. -/
theorem continuous_latticeTheta_of_lower {A : P → (d → ℝ) ≃ₗ[ℝ] (d → ℝ)}
    (hA : ∀ v, Continuous fun p => A p v) {κ : ℝ} (hκ : 0 < κ)
    (hlow : ∀ p v, κ * ‖v‖ ^ 2 ≤ sqNorm (A p v)) {t : ℝ} (ht : 0 < t) :
    Continuous fun p => latticeTheta (A p) t := by
  unfold latticeTheta
  refine continuous_tsum (u := fun m : d → ℤ => Real.exp (-(π * t * κ) * ‖intVec m‖ ^ 2))
    (fun m => ?_) (summable_exp_neg_norm_sq (by positivity)) (fun m p => ?_)
  · have hs : Continuous (sqNorm (d := d)) := by
      unfold sqNorm
      fun_prop
    exact Real.continuous_exp.comp (continuous_const.mul (hs.comp (hA (intVec m))))
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact exp_theta_term_le (A p) (hlow p) ht.le le_rfl m

theorem continuous_theta (F : ThetaFamily d P) {t : ℝ} (ht : 0 < t) :
    Continuous fun p => latticeTheta (F.A p) t :=
  continuous_latticeTheta_of_lower F.continuous_A F.κ_pos F.lower ht

theorem continuous_thetaDual (F : ThetaFamily d P) {t : ℝ} (ht : 0 < t) :
    Continuous fun p => latticeTheta (dualEquiv (F.A p)) t :=
  continuous_latticeTheta_of_lower F.continuous_dual F.κ_pos F.lower_dual ht

/-- The averaged theta function `F(t) = ∫ θ_{A_p}(t) dμ(p)`. -/
def avg (t : ℝ) : ℝ := ∫ p, latticeTheta (F.A p) t ∂μ

/-- The averaged dual theta function. -/
def avgDual (t : ℝ) : ℝ := ∫ p, latticeTheta (dualEquiv (F.A p)) t ∂μ

variable [IsFiniteMeasure μ]

theorem integrable_theta {t : ℝ} (ht : 0 < t) :
    Integrable (fun p => latticeTheta (F.A p) t) μ := by
  refine Integrable.of_bound (F.continuous_theta ht).aestronglyMeasurable
    (gaussMajorant d (π * t * F.κ)) (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (latticeTheta_nonneg _ _)]
  exact latticeTheta_le_of_lower (F.A p) F.κ_pos (F.lower p) ht le_rfl

theorem integrable_thetaDual {t : ℝ} (ht : 0 < t) :
    Integrable (fun p => latticeTheta (dualEquiv (F.A p)) t) μ := by
  refine Integrable.of_bound (F.continuous_thetaDual ht).aestronglyMeasurable
    (gaussMajorant d (π * t * F.κ)) (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (latticeTheta_nonneg _ _)]
  exact latticeTheta_le_of_lower (dualEquiv (F.A p)) F.κ_pos (F.lower_dual p) ht le_rfl

theorem continuousOn_avg_of {A : P → (d → ℝ) ≃ₗ[ℝ] (d → ℝ)}
    (hA : ∀ v, Continuous fun p => A p v) {κ : ℝ} (hκ : 0 < κ)
    (hlow : ∀ p v, κ * ‖v‖ ^ 2 ≤ sqNorm (A p v)) :
    ContinuousOn (fun t => ∫ p, latticeTheta (A p) t ∂μ) (Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  have hx' : (0 : ℝ) < x / 2 := by positivity
  have hcont : ContinuousOn (fun t => ∫ p, latticeTheta (A p) t ∂μ) (Ioi (x / 2)) := by
    refine continuousOn_of_dominated (bound := fun _ => gaussMajorant d (π * (x / 2) * κ))
      (fun t ht => ?_) (fun t ht => ae_of_all _ fun p => ?_) (integrable_const _)
      (ae_of_all _ fun p => ?_)
    · have ht0 : 0 < t := lt_trans hx' ht
      exact (continuous_latticeTheta_of_lower hA hκ hlow ht0).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (latticeTheta_nonneg _ _)]
      exact latticeTheta_le_of_lower (A p) hκ (hlow p) hx' (le_of_lt ht)
    · exact (continuousOn_latticeTheta (A p)).mono (Ioi_subset_Ioi hx'.le)
  have hmem : Ioi (x / 2) ∈ 𝓝 x := Ioi_mem_nhds (by linarith)
  exact (hcont.continuousAt hmem).continuousWithinAt

theorem continuousOn_avg : ContinuousOn (F.avg μ) (Ioi 0) :=
  continuousOn_avg_of μ F.continuous_A F.κ_pos F.lower

theorem continuousOn_avgDual : ContinuousOn (F.avgDual μ) (Ioi 0) :=
  continuousOn_avg_of μ F.continuous_dual F.κ_pos F.lower_dual

/-- **The averaged theta transformation.** -/
theorem avg_one_div {x : ℝ} (hx : 0 < x) :
    F.avg μ (1 / x) = F.covol⁻¹ * x ^ ((Fintype.card d : ℝ) / 2) * F.avgDual μ x := by
  unfold avg avgDual
  have h : ∀ p, latticeTheta (F.A p) (1 / x) =
      F.covol⁻¹ * x ^ ((Fintype.card d : ℝ) / 2) * latticeTheta (dualEquiv (F.A p)) x := by
    intro p
    rw [latticeTheta_one_div (F.A p) hx, F.abs_det p]
  simp_rw [h]
  rw [integral_const_mul]

theorem avg_sub_le {t : ℝ} (ht : 1 ≤ t) :
    |F.avg μ t - μ.real univ| ≤
      μ.real univ * (Real.exp (-(π * F.κ) * (t - 1)) * gaussMajorant d (π * F.κ)) := by
  have ht0 : 0 < t := by linarith
  have heq : F.avg μ t - μ.real univ = ∫ p, (latticeTheta (F.A p) t - 1) ∂μ := by
    rw [integral_sub (F.integrable_theta μ ht0) (integrable_const _), integral_const,
      smul_eq_mul, mul_one]
    rfl
  rw [heq, ← Real.norm_eq_abs]
  have hb := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun p => latticeTheta (F.A p) t - 1)
    (C := Real.exp (-(π * F.κ) * (t - 1)) * gaussMajorant d (π * F.κ))
    (ae_of_all _ fun p => by
      obtain ⟨h0, h1⟩ := latticeTheta_sub_one_le_of_lower (F.A p) F.κ_pos (F.lower p) ht
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1)
  linarith

theorem avgDual_sub_le {t : ℝ} (ht : 1 ≤ t) :
    |F.avgDual μ t - μ.real univ| ≤
      μ.real univ * (Real.exp (-(π * F.κ) * (t - 1)) * gaussMajorant d (π * F.κ)) := by
  have ht0 : 0 < t := by linarith
  have heq : F.avgDual μ t - μ.real univ =
      ∫ p, (latticeTheta (dualEquiv (F.A p)) t - 1) ∂μ := by
    rw [integral_sub (F.integrable_thetaDual μ ht0) (integrable_const _), integral_const,
      smul_eq_mul, mul_one]
    rfl
  rw [heq, ← Real.norm_eq_abs]
  have hb := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun p => latticeTheta (dualEquiv (F.A p)) t - 1)
    (C := Real.exp (-(π * F.κ) * (t - 1)) * gaussMajorant d (π * F.κ))
    (ae_of_all _ fun p => by
      obtain ⟨h0, h1⟩ :=
        latticeTheta_sub_one_le_of_lower (dualEquiv (F.A p)) F.κ_pos (F.lower_dual p) ht
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1)
  linarith

theorem isBigO_of_sub_le {f : ℝ → ℝ} {c M κ : ℝ} (hκ : 0 < κ)
    (h : ∀ t, 1 ≤ t → |f t - c| ≤ M * Real.exp (-(π * κ) * (t - 1))) (r : ℝ) :
    (fun t => ((f t : ℝ) : ℂ) - (c : ℂ)) =O[atTop] (· ^ r) := by
  have h1 : (fun t => f t - c) =O[atTop] fun t => Real.exp (-(π * κ) * t) := by
    refine IsBigO.of_bound (|M| * Real.exp (π * κ)) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    have e : Real.exp (-(π * κ) * (t - 1)) = Real.exp (π * κ) * Real.exp (-(π * κ) * t) := by
      rw [← Real.exp_add]
      ring_nf
    have := h t ht
    rw [e] at this
    calc |f t - c| ≤ M * (Real.exp (π * κ) * Real.exp (-(π * κ) * t)) := this
      _ ≤ |M| * (Real.exp (π * κ) * Real.exp (-(π * κ) * t)) :=
          mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)
      _ = |M| * Real.exp (π * κ) * Real.exp (-(π * κ) * t) := by ring
  have h2 := h1.trans (isLittleO_exp_neg_mul_rpow_atTop (by positivity) r).isBigO
  simpa using isBigO_ofReal_left.mpr h2

/-- **The averaged theta functions form a weak FE-pair.** -/
def fePair [Nonempty d] : WeakFEPair ℂ where
  f := fun t => ((F.avg μ t : ℝ) : ℂ)
  g := fun t => ((F.avgDual μ t : ℝ) : ℂ)
  k := (Fintype.card d : ℝ) / 2
  ε := ((F.covol⁻¹ : ℝ) : ℂ)
  f₀ := ((μ.real univ : ℝ) : ℂ)
  g₀ := ((μ.real univ : ℝ) : ℂ)
  hf_int := (continuous_ofReal.comp_continuousOn (F.continuousOn_avg μ)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn (F.continuousOn_avgDual μ)).locallyIntegrableOn
    measurableSet_Ioi
  hk := by
    have h := Fintype.card_pos (α := d)
    have : (0 : ℝ) < Fintype.card d := by exact_mod_cast h
    positivity
  hε := by
    have : (0 : ℝ) < F.covol⁻¹ := inv_pos.mpr F.covol_pos
    exact_mod_cast this.ne'
  h_feq x hx := by
    simp only [smul_eq_mul]
    rw [F.avg_one_div μ hx]
    push_cast
    ring
  hf_top r := isBigO_of_sub_le F.κ_pos (M := μ.real univ * gaussMajorant d (π * F.κ))
    (fun t ht => by
      have := F.avg_sub_le μ ht
      calc |F.avg μ t - μ.real univ|
          ≤ μ.real univ * (Real.exp (-(π * F.κ) * (t - 1)) * gaussMajorant d (π * F.κ)) := this
        _ = μ.real univ * gaussMajorant d (π * F.κ) * Real.exp (-(π * F.κ) * (t - 1)) := by
          ring) r
  hg_top r := isBigO_of_sub_le F.κ_pos (M := μ.real univ * gaussMajorant d (π * F.κ))
    (fun t ht => by
      have := F.avgDual_sub_le μ ht
      calc |F.avgDual μ t - μ.real univ|
          ≤ μ.real univ * (Real.exp (-(π * F.κ) * (t - 1)) * gaussMajorant d (π * F.κ)) := this
        _ = μ.real univ * gaussMajorant d (π * F.κ) * Real.exp (-(π * F.κ) * (t - 1)) := by
          ring) r

@[simp] theorem fePair_k [Nonempty d] : (F.fePair μ).k = (Fintype.card d : ℝ) / 2 := rfl

@[simp] theorem fePair_ε [Nonempty d] : (F.fePair μ).ε = ((F.covol⁻¹ : ℝ) : ℂ) := rfl

@[simp] theorem fePair_f₀ [Nonempty d] : (F.fePair μ).f₀ = ((μ.real univ : ℝ) : ℂ) := rfl

@[simp] theorem fePair_g₀ [Nonempty d] : (F.fePair μ).g₀ = ((μ.real univ : ℝ) : ℂ) := rfl

/-- **Functional equation of the averaged Epstein zeta function.** -/
theorem functional_equation [Nonempty d] (s : ℂ) :
    (F.fePair μ).Λ ((Fintype.card d : ℝ) / 2 - s) =
      ((F.covol⁻¹ : ℝ) : ℂ) * (F.fePair μ).symm.Λ s := by
  have := (F.fePair μ).functional_equation s
  simpa [smul_eq_mul] using this

/-- The averaged `Λ` is holomorphic away from `0` and `d/2`. -/
theorem differentiableAt_Λ [Nonempty d] {s : ℂ} (hs0 : s ≠ 0)
    (hsk : s ≠ ((Fintype.card d : ℝ) / 2 : ℝ)) :
    DifferentiableAt ℂ (F.fePair μ).Λ s :=
  (F.fePair μ).differentiableAt_Λ (Or.inl hs0) (Or.inl hsk)

/-- The residue at `s = d/2` is `μ(P) / covol`. -/
theorem residue [Nonempty d] :
    Tendsto (fun s : ℂ => (s - ((Fintype.card d : ℝ) / 2 : ℝ)) * (F.fePair μ).Λ s)
      (𝓝[≠] (((Fintype.card d : ℝ) / 2 : ℝ) : ℂ))
      (𝓝 (((F.covol⁻¹ : ℝ) : ℂ) * ((μ.real univ : ℝ) : ℂ))) := by
  have := (F.fePair μ).Λ_residue_k
  simpa [smul_eq_mul] using this

end ThetaFamily

end SimultaneousPrimitiveRoots.Hecke

end
