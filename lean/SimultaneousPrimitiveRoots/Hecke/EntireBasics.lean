module

public import SimultaneousPrimitiveRoots.Hecke.KummerGrowth
public import Mathlib.Analysis.Analytic.Order

/-!
# Basic facts about the entire function `F_K(s) = (s - 1) ζ_K(s)`

Inputs for zero counting (Jensen) and the explicit formula:

* `one_le_dedekindZeta_re`, `dedekindZeta_ofReal_im`: `ζ_K(σ)` is real and `≥ 1` for `σ > 1`.
* `one_le_norm_dedekindZetaEntire_two`: `‖F_K(2)‖ ≥ 1` (the centre of the contour circles).
* `dedekindZetaEntire_ne_zero`: `F_K(s) ≠ 0` for `Re s ≥ 1` (the project's 3-4-1 theorem
  `numberFieldNormalizedZeta_ne_zero`, transported by `dedekindZetaEntire_eqOn_normalizedZeta`).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField Module

variable (K : Type*) [Field K] [NumberField K]

theorem idealCount_one : idealCount K 1 = 1 := by
  unfold idealCount
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨⊤, Ideal.absNorm_top⟩, fun I => ?_⟩
  exact Subtype.ext (Ideal.absNorm_eq_one_iff.mp I.2)

/-- `ζ_K(σ) ≥ 1` for real `σ > 1`. -/
theorem one_le_dedekindZeta_re {σ : ℝ} (hσ : 1 < σ) : 1 ≤ (dedekindZeta K σ).re := by
  have hS := hasSum_zetaTerm K hσ
  have h1 : zetaTerm K σ 1 = 1 := by
    unfold zetaTerm
    simp [idealCount_one]
  calc (1 : ℝ) = zetaTerm K σ 1 := h1.symm
    _ ≤ (dedekindZeta K σ).re := le_hasSum hS 1 fun n _ => zetaTerm_nonneg K σ n

/-- `ζ_K(σ)` is real for real `σ > 1`. -/
theorem dedekindZeta_ofReal_im {σ : ℝ} (hσ : 1 < σ) : (dedekindZeta K σ).im = 0 := by
  rw [TauCeti.dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub hσ, Complex.ofReal_im]

/-- `‖F_K(2)‖ ≥ 1`. -/
theorem one_le_norm_dedekindZetaEntire_two : 1 ≤ ‖dedekindZetaEntire K 2‖ := by
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  rw [dedekindZetaEntire_eq_mul K h2, show (2 : ℂ) - 1 = 1 by norm_num, one_mul]
  have hre := one_le_dedekindZeta_re K (σ := 2) (by norm_num)
  have him := dedekindZeta_ofReal_im K (σ := 2) (by norm_num)
  have hcast : ((2 : ℝ) : ℂ) = 2 := by norm_num
  rw [hcast] at hre him
  calc (1 : ℝ) ≤ (dedekindZeta K 2).re := hre
    _ ≤ |(dedekindZeta K 2).re| := le_abs_self _
    _ ≤ ‖dedekindZeta K 2‖ := Complex.abs_re_le_norm _

/-- **`F_K(s) ≠ 0` for `Re s ≥ 1`.** -/
theorem dedekindZetaEntire_ne_zero {s : ℂ} (hs : 1 ≤ s.re) : dedekindZetaEntire K s ≠ 0 := by
  rw [dedekindZetaEntire_eqOn_normalizedZeta K (numberFieldZetaContinuationDomain_mem K hs)]
  exact numberFieldNormalizedZeta_ne_zero K hs

/-- `F_K` is not identically zero near any point. -/
theorem dedekindZetaEntire_analyticOrderAt_ne_top (z : ℂ) :
    analyticOrderAt (dedekindZetaEntire K) z ≠ ⊤ := by
  have hF : AnalyticOnNhd ℂ (dedekindZetaEntire K) Set.univ :=
    fun w _ => (differentiable_dedekindZetaEntire K).analyticAt w
  have h2 : dedekindZetaEntire K 2 ≠ 0 := dedekindZetaEntire_ne_zero K (by norm_num)
  have htwo : analyticOrderAt (dedekindZetaEntire K) (2 : ℂ) = 0 :=
    (hF 2 (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr h2
  exact hF.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ _) (Set.mem_univ _) (by rw [htwo]; simp)

end SimultaneousPrimitiveRoots.Hecke

end
