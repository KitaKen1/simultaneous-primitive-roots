module

public import SimultaneousPrimitiveRoots.Hecke.GaussianTheta
public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

/-!
# B7 step E1: the theta function of a lattice `A ℤ^d` as a `WeakFEPair`.

The theta transformation `tsum_gaussian_eq` (D2) is exactly the functional equation needed by
Mathlib's abstract Mellin machinery (`Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean`).
The result is the analytic continuation and functional equation of the Epstein zeta function
`∑_{m ≠ 0} |A m|^{-2s}`: this is Riemann's second proof, in `d` variables.

For a number field the Dedekind zeta function is an average of such Epstein zeta functions over
the compact torus of norm-one weights modulo units (Hecke); that is step D3.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Hecke

open MeasureTheory Set Function Filter Complex Asymptotics
open scoped Real Topology

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The real theta function `t ↦ ∑_m exp(-π t |A m|²)` of the lattice `A ℤ^d`. -/
noncomputable def latticeTheta (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (t : ℝ) : ℝ :=
  ∑' m : d → ℤ, Real.exp (-(π * t) * sqNorm (A (intVec m)))

omit [DecidableEq d] in
/-- Domination of the theta terms for `t ≥ t₀ ≥ 0`. -/
theorem exp_theta_term_le (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {κ : ℝ}
    (hκA : ∀ v : d → ℝ, κ * ‖v‖ ^ 2 ≤ sqNorm (A v)) {t₀ t : ℝ} (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t)
    (m : d → ℤ) :
    Real.exp (-(π * t) * sqNorm (A (intVec m))) ≤
      Real.exp (-(π * t₀ * κ) * ‖intVec m‖ ^ 2) := by
  apply Real.exp_le_exp.mpr
  have h1 := hκA (intVec m)
  have h2 := sqNorm_nonneg (A (intVec m))
  have hp : 0 ≤ π * t₀ := by positivity
  have h3 : π * t₀ * (κ * ‖intVec m‖ ^ 2) ≤ π * t * sqNorm (A (intVec m)) := by
    calc π * t₀ * (κ * ‖intVec m‖ ^ 2) ≤ π * t₀ * sqNorm (A (intVec m)) :=
          mul_le_mul_of_nonneg_left h1 hp
      _ ≤ π * t * sqNorm (A (intVec m)) := by
          apply mul_le_mul_of_nonneg_right _ h2
          exact mul_le_mul_of_nonneg_left ht Real.pi_pos.le
  have e1 : -(π * t) * sqNorm (A (intVec m)) = -(π * t * sqNorm (A (intVec m))) := by ring
  have e2 : -(π * t₀ * κ) * ‖intVec m‖ ^ 2 = -(π * t₀ * (κ * ‖intVec m‖ ^ 2)) := by ring
  rw [e1, e2]
  linarith

theorem summable_theta (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {t : ℝ} (ht : 0 < t) :
    Summable fun m : d → ℤ => Real.exp (-(π * t) * sqNorm (A (intVec m))) := by
  obtain ⟨κ, hκ, hκA⟩ := exists_sqNorm_lower A
  exact Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
    (exp_theta_term_le A hκA ht.le le_rfl)
    (summable_exp_neg_norm_sq (by positivity))

theorem continuousOn_latticeTheta (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) :
    ContinuousOn (latticeTheta A) (Ioi 0) := by
  obtain ⟨κ, hκ, hκA⟩ := exists_sqNorm_lower A
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  have hx' : (0 : ℝ) < x / 2 := by positivity
  have hcont : ContinuousOn (fun t : ℝ => ∑' m : d → ℤ,
      Real.exp (-(π * t) * sqNorm (A (intVec m)))) (Ioi (x / 2)) := by
    refine continuousOn_tsum
      (u := fun m : d → ℤ => Real.exp (-(π * (x / 2) * κ) * ‖intVec m‖ ^ 2))
      (fun m => ?_) (summable_exp_neg_norm_sq (by positivity)) (fun m t ht => ?_)
    · exact (Continuous.continuousOn (by fun_prop))
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact exp_theta_term_le A hκA hx'.le (le_of_lt ht) m
  have hmem : Ioi (x / 2) ∈ 𝓝 x := Ioi_mem_nhds (by linarith)
  exact (hcont.continuousAt hmem).continuousWithinAt

omit [DecidableEq d] in
theorem sqNorm_pos_of_ne (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {m : d → ℤ} (hm : m ≠ 0) :
    0 < sqNorm (A (intVec m)) := by
  obtain ⟨κ, hκ, hκA⟩ := exists_sqNorm_lower A
  have h1 := one_le_norm_intVec hm
  have h2 : 1 ≤ ‖intVec m‖ ^ 2 := by nlinarith
  have := hκA (intVec m)
  nlinarith

omit [DecidableEq d] in
theorem sqNorm_intVec_zero (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) :
    sqNorm (A (intVec (0 : d → ℤ))) = 0 := by
  have h0 : intVec (0 : d → ℤ) = 0 := by
    funext i
    simp [intVec]
  simp [h0, sqNorm]

/-- Exponential decay of `θ_A(t) - 1`. -/
theorem latticeTheta_sub_one_le (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ t : ℝ, 1 ≤ t →
      0 ≤ latticeTheta A t - 1 ∧
        latticeTheta A t - 1 ≤ Real.exp (-(π * κ) * (t - 1)) * latticeTheta A 1 := by
  obtain ⟨κ, hκ, hκA⟩ := exists_sqNorm_lower A
  refine ⟨κ, hκ, fun t ht => ?_⟩
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
  -- termwise bound
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
  rw [hsplit 1 hsum_1]
  linarith

theorem isBigO_latticeTheta_sub_one (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) :
    ∃ p : ℝ, 0 < p ∧
      (fun t => latticeTheta A t - 1) =O[atTop] fun t => Real.exp (-p * t) := by
  obtain ⟨κ, hκ, hbound⟩ := latticeTheta_sub_one_le A
  refine ⟨π * κ, by positivity, ?_⟩
  refine IsBigO.of_bound (Real.exp (π * κ) * latticeTheta A 1) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  obtain ⟨h0, h1⟩ := hbound t ht
  rw [Real.norm_eq_abs, abs_of_nonneg h0, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  have e : Real.exp (-(π * κ) * (t - 1)) = Real.exp (π * κ) * Real.exp (-(π * κ) * t) := by
    rw [← Real.exp_add]
    ring_nf
  rw [e] at h1
  linarith

/-- The theta functional equation in the form required by `WeakFEPair`. -/
theorem latticeTheta_one_div (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {x : ℝ} (hx : 0 < x) :
    latticeTheta A (1 / x) = |LinearMap.det (A : (d → ℝ) →ₗ[ℝ] (d → ℝ))|⁻¹ *
      x ^ ((Fintype.card d : ℝ) / 2) * latticeTheta (dualEquiv A) x := by
  have h := tsum_gaussian_eq A (one_div_pos.mpr hx)
  rw [one_div_one_div] at h
  unfold latticeTheta
  rw [h]
  congr 1
  apply tsum_congr
  intro n
  congr 1
  rw [div_eq_mul_inv, one_div, inv_inv]
  ring

omit [Fintype d] [DecidableEq d] in
theorem det_ne_zero (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) :
    LinearMap.det (A : (d → ℝ) →ₗ[ℝ] (d → ℝ)) ≠ 0 :=
  (LinearEquiv.isUnit_det' A).ne_zero

/-- **The lattice theta function is a weak FE-pair** (`k = d/2`, `ε = |det A|⁻¹`). -/
noncomputable def thetaFEPair (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) [Nonempty d] : WeakFEPair ℂ where
  f := fun t => ((latticeTheta A t : ℝ) : ℂ)
  g := fun t => ((latticeTheta (dualEquiv A) t : ℝ) : ℂ)
  k := (Fintype.card d : ℝ) / 2
  ε := ((|LinearMap.det (A : (d → ℝ) →ₗ[ℝ] (d → ℝ))|⁻¹ : ℝ) : ℂ)
  f₀ := 1
  g₀ := 1
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_latticeTheta A)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn
    (continuousOn_latticeTheta (dualEquiv A))).locallyIntegrableOn measurableSet_Ioi
  hk := by
    have h := Fintype.card_pos (α := d)
    have : (0 : ℝ) < Fintype.card d := by exact_mod_cast h
    positivity
  hε := by
    have h := det_ne_zero A
    have : (0 : ℝ) < |LinearMap.det (A : (d → ℝ) →ₗ[ℝ] (d → ℝ))|⁻¹ := by positivity
    exact_mod_cast this.ne'
  h_feq x hx := by
    simp only [smul_eq_mul]
    rw [latticeTheta_one_div A hx]
    push_cast
    ring
  hf_top r := by
    obtain ⟨p, hp, hp'⟩ := isBigO_latticeTheta_sub_one A
    simpa using isBigO_ofReal_left.mpr <| hp'.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO
  hg_top r := by
    obtain ⟨p, hp, hp'⟩ := isBigO_latticeTheta_sub_one (dualEquiv A)
    simpa using isBigO_ofReal_left.mpr <| hp'.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO

@[simp] theorem thetaFEPair_k (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) [Nonempty d] :
    (thetaFEPair A).k = (Fintype.card d : ℝ) / 2 := rfl

@[simp] theorem thetaFEPair_ε (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) [Nonempty d] :
    (thetaFEPair A).ε = ((|LinearMap.det (A : (d → ℝ) →ₗ[ℝ] (d → ℝ))|⁻¹ : ℝ) : ℂ) := rfl

@[simp] theorem thetaFEPair_f₀ (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) [Nonempty d] :
    (thetaFEPair A).f₀ = 1 := rfl

@[simp] theorem thetaFEPair_g₀ (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) [Nonempty d] :
    (thetaFEPair A).g₀ = 1 := rfl

/-- Summability of the Epstein series `∑ |A m|^{-2σ}` for `2σ > d`. -/
theorem summable_epstein (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {σ : ℝ}
    (hσ : (Fintype.card d : ℝ) / 2 < σ) :
    Summable fun m : d → ℤ => ‖(1 : ℂ)‖ / sqNorm (A (intVec m)) ^ σ := by
  obtain ⟨κ, hκ, hκA⟩ := exists_sqNorm_lower A
  have hσ0 : 0 < σ := lt_of_le_of_lt (by positivity) hσ
  have hr : -(2 * σ) < -(Module.finrank ℤ (intSpan d) : ℝ) := by
    rw [finrank_intSpan]
    linarith
  have hL := ZLattice.summable_norm_rpow (intSpan d) (-(2 * σ)) hr
  have hL' : Summable fun m : d → ℤ => κ ^ (-σ) * ‖intVec m‖ ^ (-(2 * σ)) := by
    have := (intSpanEquiv (d := d)).summable_iff.mpr hL
    exact this.mul_left _
  refine Summable.of_nonneg_of_le
    (fun m => div_nonneg (norm_nonneg _) (Real.rpow_nonneg (sqNorm_nonneg _) _)) (fun m => ?_) hL'
  rw [norm_one]
  by_cases hm : m = 0
  · subst hm
    rw [sqNorm_intVec_zero, Real.zero_rpow hσ0.ne', div_zero]
    positivity
  · have hpos := sqNorm_pos_of_ne A hm
    have hn := one_le_norm_intVec hm
    have hn0 : 0 < ‖intVec m‖ := by linarith
    have hlow : κ * ‖intVec m‖ ^ 2 ≤ sqNorm (A (intVec m)) := hκA (intVec m)
    have hκn : 0 < κ * ‖intVec m‖ ^ 2 := by positivity
    have hmono : (κ * ‖intVec m‖ ^ 2) ^ σ ≤ sqNorm (A (intVec m)) ^ σ :=
      Real.rpow_le_rpow hκn.le hlow hσ0.le
    have heq : κ ^ (-σ) * ‖intVec m‖ ^ (-(2 * σ)) = 1 / (κ * ‖intVec m‖ ^ 2) ^ σ := by
      rw [Real.mul_rpow hκ.le (by positivity), Real.rpow_neg hκ.le, ← Real.rpow_natCast,
        ← Real.rpow_mul hn0.le, Real.rpow_neg hn0.le]
      push_cast
      field_simp
    rw [heq]
    exact one_div_le_one_div_of_le (by positivity) hmono

/-- The Mellin transform of `θ_A - 1` is the completed Epstein series. -/
theorem hasSum_mellin_latticeTheta (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {s : ℂ}
    (hs : (Fintype.card d : ℝ) / 2 < s.re) :
    HasSum (fun m : d → ℤ => π ^ (-s) * Gamma s * 1 / ((sqNorm (A (intVec m)) : ℝ) : ℂ) ^ s)
      (mellin (fun t => ((latticeTheta A t : ℝ) : ℂ) - 1) s) := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  refine hasSum_mellin_pi_mul₀ (a := fun _ => (1 : ℂ)) (p := fun m => sqNorm (A (intVec m)))
    (fun m => sqNorm_nonneg _) hs0 (fun t ht => ?_) (summable_epstein A hs)
  have ht0 : (0 : ℝ) < t := ht
  have h := (summable_theta A ht0).hasSum.update (0 : d → ℤ) 0
  have hg0 : Real.exp (-(π * t) * sqNorm (A (intVec (0 : d → ℤ)))) = 1 := by
    simp [sqNorm_intVec_zero]
  rw [hg0] at h
  have h' := Complex.hasSum_ofReal.mpr h
  convert h' using 1
  · funext m
    by_cases hm : m = 0
    · subst hm
      simp [sqNorm_intVec_zero]
    · have hp := (sqNorm_pos_of_ne A hm).ne'
      simp only [hp, ite_false, one_mul, update_of_ne hm]
      congr 2
      ring
  · simp [latticeTheta]
    ring

/-- **Epstein zeta, continuation**: `Λ_A` is meromorphic with poles at most at `0` and `d/2`, and
equals the completed Epstein series `π^{-s} Γ(s) ∑_{m ≠ 0} |A m|^{-2s}` for `re s > d/2`. -/
theorem hasSum_epstein (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) [Nonempty d] {s : ℂ}
    (hs : (Fintype.card d : ℝ) / 2 < s.re) :
    HasSum (fun m : d → ℤ => π ^ (-s) * Gamma s * 1 / ((sqNorm (A (intVec m)) : ℝ) : ℂ) ^ s)
      ((thetaFEPair A).Λ s) := by
  have hM := (thetaFEPair A).hasMellin (s := s) hs
  rw [← hM.2]
  exact hasSum_mellin_latticeTheta A hs

/-- The dual side of the Epstein functional equation. -/
theorem hasSum_epstein_dual (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) [Nonempty d] {s : ℂ}
    (hs : (Fintype.card d : ℝ) / 2 < s.re) :
    HasSum (fun n : d → ℤ =>
        π ^ (-s) * Gamma s * 1 / ((sqNorm (dualEquiv A (intVec n)) : ℝ) : ℂ) ^ s)
      ((thetaFEPair A).symm.Λ s) := by
  have hM := (thetaFEPair A).symm.hasMellin (s := s) hs
  rw [← hM.2]
  exact hasSum_mellin_latticeTheta (dualEquiv A) hs

/-- **Epstein zeta, functional equation**: `Λ_A(d/2 - s) = |det A|⁻¹ Λ_{A^∨}(s)`. -/
theorem epstein_functional_equation (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) [Nonempty d] (s : ℂ) :
    (thetaFEPair A).Λ ((Fintype.card d : ℝ) / 2 - s) =
      ((|LinearMap.det (A : (d → ℝ) →ₗ[ℝ] (d → ℝ))|⁻¹ : ℝ) : ℂ) * (thetaFEPair A).symm.Λ s := by
  have := (thetaFEPair A).functional_equation s
  simpa [smul_eq_mul] using this

/-- `Λ_A` is holomorphic away from `0` and `d/2`. -/
theorem differentiableAt_epstein (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) [Nonempty d] {s : ℂ}
    (hs0 : s ≠ 0) (hsk : s ≠ ((Fintype.card d : ℝ) / 2 : ℝ)) :
    DifferentiableAt ℂ (thetaFEPair A).Λ s :=
  (thetaFEPair A).differentiableAt_Λ (Or.inl hs0) (Or.inl hsk)

/-- The residue of `Λ_A` at `s = d/2` is `|det A|⁻¹`. -/
theorem epstein_residue (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) [Nonempty d] :
    Tendsto (fun s : ℂ => (s - ((Fintype.card d : ℝ) / 2 : ℝ)) * (thetaFEPair A).Λ s)
      (𝓝[≠] (((Fintype.card d : ℝ) / 2 : ℝ) : ℂ))
      (𝓝 ((|LinearMap.det (A : (d → ℝ) →ₗ[ℝ] (d → ℝ))|⁻¹ : ℝ) : ℂ)) := by
  have := (thetaFEPair A).Λ_residue_k
  simpa [smul_eq_mul] using this

end SimultaneousPrimitiveRoots.Hecke
