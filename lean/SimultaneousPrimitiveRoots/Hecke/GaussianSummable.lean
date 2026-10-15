module

public import SimultaneousPrimitiveRoots.Hecke.PoissonTorus
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Complex.Exponential

/-!
# Gaussian sums over `ℤ^d` converge

For `a > 0`, `∑_{m ∈ ℤ^d} exp(-a ‖m‖²)` converges (sup norm). Together with a lower bound
`|A v|² ≥ κ ‖v‖²` for an invertible linear map `A`, this gives the summability hypotheses of
Poisson summation for the Gaussian `exp(-π t |A u|²)`, uniformly on compact sets of `u`.
-/

@[expose] public section
noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open MeasureTheory Set Function Filter TopologicalSpace ContinuousMap
open scoped Real Nat

variable {d : Type*} [Fintype d]

/-- The Euclidean square norm `∑ xᵢ²` on `d → ℝ`. -/
def sqNorm (x : d → ℝ) : ℝ := ∑ i, x i ^ 2

theorem sqNorm_nonneg (x : d → ℝ) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg fun i _ => sq_nonneg (x i)

/-- The sup norm squared is at most the Euclidean square norm. -/
theorem norm_sq_le_sqNorm (x : d → ℝ) : ‖x‖ ^ 2 ≤ sqNorm x := by
  have h : ‖x‖ ≤ Real.sqrt (sqNorm x) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    exact Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j))
      (Finset.mem_univ i)
  have h0 : 0 ≤ ‖x‖ := norm_nonneg x
  calc ‖x‖ ^ 2 ≤ Real.sqrt (sqNorm x) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = sqNorm x := Real.sq_sqrt (sqNorm_nonneg x)

/-- A nonzero integer vector has sup norm at least one. -/
theorem one_le_norm_intVec {m : d → ℤ} (hm : m ≠ 0) : 1 ≤ ‖intVec m‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hm
  have h1 : (1 : ℝ) ≤ |(m i : ℝ)| := by
    have : (1 : ℤ) ≤ |m i| := Int.one_le_abs hi
    exact_mod_cast this
  calc (1 : ℝ) ≤ |(m i : ℝ)| := h1
    _ = ‖intVec m i‖ := by simp [intVec]
    _ ≤ ‖intVec m‖ := norm_le_pi_norm (intVec m) i

/-- The `ℤ`-span of the standard basis, as a submodule (for the lattice `p`-series). -/
abbrev intSpan (d : Type*) [Fintype d] : Submodule ℤ (d → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ d))

/-- `ℤ^d` is indexed by `d → ℤ`, now as a submodule. -/
def intSpanEquiv : (d → ℤ) ≃ intSpan d :=
  (intLatticeEquiv (d := d)).trans (Equiv.subtypeEquivRight fun _ => Iff.rfl)

theorem intSpanEquiv_coe (m : d → ℤ) : ((intSpanEquiv m : intSpan d) : d → ℝ) = intVec m :=
  rfl

theorem finrank_intSpan : Module.finrank ℤ (intSpan d) = Fintype.card d := by
  rw [ZLattice.rank ℝ (intSpan d)]
  simp

/-- `exp(-a s²) ≤ (k!/aᵏ) s⁻ᵏ` for `s ≥ 1`. -/
theorem exp_neg_sq_le_rpow {a s : ℝ} (ha : 0 < a) (hs : 1 ≤ s) (k : ℕ) :
    Real.exp (-a * s ^ 2) ≤ ((k ! : ℝ) / a ^ k) * s ^ (-(k : ℝ)) := by
  have hs0 : 0 < s := by linarith
  have hx : 0 ≤ a * s ^ 2 := by positivity
  have hfac := Real.pow_div_factorial_le_exp _ hx k
  have hk : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hpos : 0 < (a * s ^ 2) ^ k := by positivity
  -- exp(-a s²) = 1 / exp(a s²) ≤ k! / (a s²)^k
  have h1 : Real.exp (-a * s ^ 2) ≤ (k ! : ℝ) / (a * s ^ 2) ^ k := by
    rw [neg_mul, Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) hpos]
    have := (div_le_iff₀ hk).mp hfac
    linarith
  -- (a s²)^k ≥ a^k s^k since s ≥ 1
  have h2 : (k ! : ℝ) / (a * s ^ 2) ^ k ≤ ((k ! : ℝ) / a ^ k) * s ^ (-(k : ℝ)) := by
    have hsk : s ^ k ≤ s ^ (2 * k) := pow_le_pow_right₀ hs (by omega)
    have hak : 0 < a ^ k := by positivity
    have hR : ((k ! : ℝ) / a ^ k) * (s ^ k)⁻¹ = (k ! : ℝ) / (a ^ k * s ^ k) := by
      field_simp
    have hL : (k ! : ℝ) / (a * s ^ 2) ^ k = (k ! : ℝ) / (a ^ k * s ^ (2 * k)) := by
      rw [mul_pow, ← pow_mul]
    rw [Real.rpow_neg hs0.le, Real.rpow_natCast, hR, hL]
    exact div_le_div_of_nonneg_left hk.le (by positivity)
      (mul_le_mul_of_nonneg_left hsk hak.le)
  exact h1.trans h2

/-- **Gaussian sums over `ℤ^d` converge.** -/
theorem summable_exp_neg_norm_sq {a : ℝ} (ha : 0 < a) :
    Summable fun m : d → ℤ => Real.exp (-a * ‖intVec m‖ ^ 2) := by
  classical
  set k : ℕ := Fintype.card d + 1 with hk
  have hr : (-(k : ℝ)) < -(Module.finrank ℤ (intSpan d) : ℝ) := by
    rw [finrank_intSpan, hk]
    push_cast
    linarith
  have hL := ZLattice.summable_norm_rpow (intSpan d) (-(k : ℝ)) hr
  have hL' : Summable fun m : d → ℤ =>
      ((k ! : ℝ) / a ^ k) * ‖intVec m‖ ^ (-(k : ℝ)) := by
    have := (intSpanEquiv (d := d)).summable_iff.mpr hL
    exact this.mul_left _
  refine Summable.of_norm_bounded_eventually hL' ?_
  have hfin : {m : d → ℤ | m = 0}.Finite := Set.finite_singleton 0
  filter_upwards [hfin.compl_mem_cofinite] with m hm
  have hm0 : m ≠ 0 := hm
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  exact exp_neg_sq_le_rpow ha (one_le_norm_intVec hm0) k

/-- A lower bound `κ ‖v‖² ≤ |A v|²` for an invertible linear map. -/
theorem exists_sqNorm_lower (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ v : d → ℝ, κ * ‖v‖ ^ 2 ≤ sqNorm (A v) := by
  let Ac := A.toContinuousLinearEquiv
  set N : ℝ := ‖(Ac.symm : (d → ℝ) →L[ℝ] (d → ℝ))‖ + 1 with hN
  have hN0 : 0 < N := by positivity
  refine ⟨1 / N ^ 2, by positivity, fun v => ?_⟩
  have hv : ‖v‖ ≤ N * ‖A v‖ := by
    have h1 : (Ac.symm : (d → ℝ) →L[ℝ] (d → ℝ)) (A v) = v := by simp [Ac]
    calc ‖v‖ = ‖(Ac.symm : (d → ℝ) →L[ℝ] (d → ℝ)) (A v)‖ := by rw [h1]
      _ ≤ ‖(Ac.symm : (d → ℝ) →L[ℝ] (d → ℝ))‖ * ‖A v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ N * ‖A v‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          linarith
  have hsq : ‖v‖ ^ 2 ≤ N ^ 2 * ‖A v‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg v) hv 2
    calc ‖v‖ ^ 2 ≤ (N * ‖A v‖) ^ 2 := this
      _ = N ^ 2 * ‖A v‖ ^ 2 := by ring
  have hA := norm_sq_le_sqNorm (A v)
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith

/-- `‖x + v‖² ≥ ‖v‖²/2 - ‖x‖²`. -/
theorem half_norm_sq_sub_le (x v : d → ℝ) : ‖v‖ ^ 2 / 2 - ‖x‖ ^ 2 ≤ ‖x + v‖ ^ 2 := by
  have h1 : ‖v‖ - ‖x‖ ≤ ‖x + v‖ := by
    have := norm_sub_norm_le v (-x)
    simp only [sub_neg_eq_add, norm_neg] at this
    rw [add_comm] at this
    exact this
  have h0 : 0 ≤ ‖x + v‖ := norm_nonneg _
  by_cases h : ‖x‖ ≤ ‖v‖
  · have h2 : (‖v‖ - ‖x‖) ^ 2 ≤ ‖x + v‖ ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    nlinarith [sq_nonneg (‖v‖ - 2 * ‖x‖)]
  · push Not at h
    nlinarith [norm_nonneg v, norm_nonneg x]

/-- The Gaussian `u ↦ exp(-c |A u|²)` as a continuous complex function. -/
def gaussianCM (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (c : ℝ) : C(d → ℝ, ℂ) :=
  ⟨fun u => ((Real.exp (-c * sqNorm (A u)) : ℝ) : ℂ), by
    have hA : Continuous (A : (d → ℝ) → (d → ℝ)) := A.toLinearMap.continuous_of_finiteDimensional
    have hs : Continuous (sqNorm (d := d)) := by
      unfold sqNorm
      fun_prop
    exact Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul (hs.comp hA)))⟩

theorem gaussianCM_apply (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (c : ℝ) (u : d → ℝ) :
    gaussianCM A c u = ((Real.exp (-c * sqNorm (A u)) : ℝ) : ℂ) := rfl

/-- **Gaussian translates are summable uniformly on compact sets.** -/
theorem translatesSummable_gaussian (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {c : ℝ} (hc : 0 < c) :
    TranslatesSummable (gaussianCM A c) := by
  intro K
  obtain ⟨κ, hκ, hκA⟩ := exists_sqNorm_lower A
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.exists_norm_le
  set R' : ℝ := max R 0 with hR'
  have hsum := (summable_exp_neg_norm_sq (d := d) (a := c * κ / 2) (by positivity)).mul_left
    (Real.exp (c * κ * R' ^ 2))
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) hsum
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro x
  rw [ContinuousMap.restrict_apply, ContinuousMap.comp_apply, ContinuousMap.coe_addRight,
    gaussianCM_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  have hxR : ‖(x : d → ℝ)‖ ≤ R' := (hR x x.2).trans (le_max_left _ _)
  have hlow := hκA ((x : d → ℝ) + intVec m)
  have hhalf := half_norm_sq_sub_le (x : d → ℝ) (intVec m)
  have hx2 : ‖(x : d → ℝ)‖ ^ 2 ≤ R' ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxR 2
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hκx : κ * (‖intVec m‖ ^ 2 / 2 - R' ^ 2) ≤ sqNorm (A ((x : d → ℝ) + intVec m)) := by
    calc κ * (‖intVec m‖ ^ 2 / 2 - R' ^ 2)
        ≤ κ * ‖(x : d → ℝ) + intVec m‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hκ.le
          linarith
      _ ≤ sqNorm (A ((x : d → ℝ) + intVec m)) := hlow
  nlinarith

end SimultaneousPrimitiveRoots.Hecke
