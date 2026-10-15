module

public import SimultaneousPrimitiveRoots.Hecke.DedekindContinuation
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# `(s - 1) ζ_K(s)` is entire

Write each Hecke `Λ_c` as `Λ₀_c(s') - 1/s' - ε_c/(n/2 - s')` with `Λ₀_c` entire
(`WeakFEPair.differentiable_Λ₀`). At `s = 0` the pole of `1/s'` is cancelled by the factor
`Γ(0)⁻¹ = 0` of the entire coefficient `zetaCoef` (a removable singularity, `dslope`). At `s = 1`
the factor `s - 1` cancels the pole of `ε_c/(n/2 - s')`. Hence `(s - 1) ζ_K(s)` continues to an
entire function.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField Ideal NumberField.Units Module Filter Topology
open scoped nonZeroDivisors Real

variable (K : Type*) [Field K] [NumberField K]

theorem zetaCoef_zero (c : ClassGroup (𝓞 K)) : zetaCoef K c 0 = 0 := by
  unfold zetaCoef
  have h : ∏ o, ((placeMult (K := K) o : ℝ) : ℂ) ^ ((0 : ℂ) * placeMult (K := K) o / 2) *
      (Complex.Gamma ((0 : ℂ) * placeMult (K := K) o / 2))⁻¹ = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ none)
    simp [Complex.Gamma_zero]
  rw [h]
  simp

theorem classFEPair_f₀ (c : ClassGroup (𝓞 K)) : (classFEPair K c).f₀ = 1 := by
  unfold classFEPair heckeFEPair
  rw [ThetaFamily.fePair_f₀, heckeMeasure_real_univ, Complex.ofReal_one]

theorem classFEPair_g₀ (c : ClassGroup (𝓞 K)) : (classFEPair K c).g₀ = 1 := by
  unfold classFEPair heckeFEPair
  rw [ThetaFamily.fePair_g₀, heckeMeasure_real_univ, Complex.ofReal_one]

theorem classFEPair_k (c : ClassGroup (𝓞 K)) :
    (classFEPair K c).k = (finrank ℚ K : ℝ) / 2 := by
  unfold classFEPair heckeFEPair
  rw [ThetaFamily.fePair_k, card_classIdx_eq_finrank]

/-- The entire function `(s - 1) ζ_K(s)`. -/
def dedekindZetaEntire (s : ℂ) : ℂ :=
  ∑ c : ClassGroup (𝓞 K),
    ((s - 1) * zetaCoef K c s * (classFEPair K c).Λ₀ ((finrank ℚ K : ℂ) * s / 2) -
      (2 / (finrank ℚ K : ℂ)) * (s - 1) * dslope (zetaCoef K c) 0 s +
      (2 / (finrank ℚ K : ℂ)) * (classFEPair K c).ε * zetaCoef K c s)

theorem differentiable_dedekindZetaEntire : Differentiable ℂ (dedekindZetaEntire K) := by
  intro s
  unfold dedekindZetaEntire
  refine DifferentiableAt.fun_sum (u := Finset.univ) fun c _ => ?_
  have hcoef := differentiable_zetaCoef K c
  have hΛ₀ : Differentiable ℂ fun s : ℂ => (classFEPair K c).Λ₀ ((finrank ℚ K : ℂ) * s / 2) :=
    (classFEPair K c).differentiable_Λ₀.comp (by fun_prop)
  have hd : Differentiable ℂ (dslope (zetaCoef K c) 0) := by
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
    exact hcoef.differentiableOn
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (s - 1) * zetaCoef K c s *
      (classFEPair K c).Λ₀ ((finrank ℚ K : ℂ) * s / 2)) s :=
    (((differentiableAt_id.sub_const 1).mul (hcoef s)).mul (hΛ₀ s))
  have h2 : DifferentiableAt ℂ (fun s : ℂ => (2 / (finrank ℚ K : ℂ)) * (s - 1) *
      dslope (zetaCoef K c) 0 s) s :=
    ((differentiableAt_const _).mul (differentiableAt_id.sub_const 1)).mul (hd s)
  have h3 : DifferentiableAt ℂ (fun s : ℂ => (2 / (finrank ℚ K : ℂ)) * (classFEPair K c).ε *
      zetaCoef K c s) s :=
    (differentiableAt_const _).mul (hcoef s)
  exact (h1.sub h2).add h3

theorem dedekindZetaEntire_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    dedekindZetaEntire K s = (s - 1) * dedekindZetaHecke K s := by
  have hn : (finrank ℚ K : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  unfold dedekindZetaEntire dedekindZetaHecke
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  have hΛ : (classFEPair K c).Λ ((finrank ℚ K : ℂ) * s / 2) =
      (classFEPair K c).Λ₀ ((finrank ℚ K : ℂ) * s / 2) -
        (1 / ((finrank ℚ K : ℂ) * s / 2)) * 1 -
        ((classFEPair K c).ε / ((finrank ℚ K : ℂ) / 2 - (finrank ℚ K : ℂ) * s / 2)) * 1 := by
    rw [WeakFEPair.Λ, classFEPair_f₀, classFEPair_g₀, classFEPair_k]
    simp only [smul_eq_mul]
    push_cast
    ring
  have hds : dslope (zetaCoef K c) 0 s = zetaCoef K c s / s := by
    rw [dslope_of_ne _ hs0, slope_def_field, zetaCoef_zero, sub_zero, sub_zero]
  rw [hΛ, hds]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have h1s : (finrank ℚ K : ℂ) / 2 - (finrank ℚ K : ℂ) * s / 2 ≠ 0 := by
    intro h
    apply hs1'
    have : (finrank ℚ K : ℂ) * (1 - s) = 0 := by linear_combination 2 * h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hn
    · linear_combination -h'
  field_simp
  ring

/-- **`(s - 1) ζ_K(s)` extends to an entire function.** -/
theorem exists_entire_sub_one_mul_dedekindZeta :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ s, 1 < s.re → F s = (s - 1) * dedekindZeta K s := by
  refine ⟨dedekindZetaEntire K, differentiable_dedekindZetaEntire K, fun s hs => ?_⟩
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    linarith
  rw [dedekindZetaEntire_eq K hs0 hs1, dedekindZetaHecke_eq K hs]

end SimultaneousPrimitiveRoots.Hecke

end
