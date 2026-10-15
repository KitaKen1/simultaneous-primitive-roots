module

public import SimultaneousPrimitiveRoots.Unconditional.TwoEvaluations
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# [A]'s two evaluations from the section-level estimates (top of level 4 of step Z6)

[A] (`A-02a:0123–0164`, `A-06:0648–0674`) obtains the two evaluations of the common signal `I_Z`
from estimates proved in separate sections:

* **First evaluation.** `I_Z` pairs the coefficient sums `B_m(Z)` with an additive factor, averaged
  over the compact group `F_S^1 / U_S^6`. The reflected second moment (`prop:reflection`) gives
  `∑_m |B_m(Z)|² ≪ Z^{2M₀-1+ε}`, the additive factor has squared row mass `O(Y^{-1}) = O(Z^{-b})`,
  both uniformly in the average, and Cauchy–Schwarz gives `I_Z ≪ Z^{(2M₀-1-b)/2+ε}`
  (`isBigO_of_secondMoments`). With `M₀ = 1033/1000`, `b = 133/1000` the exponent is `933/2000`.
* **Second evaluation.** After Poisson summation `I_Z - c₀ f_η(Z)` is a sum of six terms, each
  `≪ Z^{7/15 - margin + ε}` with the margins of `tab:analytic-margins`
  (`isBigO_sub_of_poissonContributions`); all margins exceed `5/10000`.

`hasTwoEvaluations_of_sectionEstimates` combines them into `HasTwoEvaluations`. This file fixes
the interface between the reflection sections ([A] §§3–4), the Poisson and zero-density sections
([A] §§5–6) and the Mellin argument already formalized in `TwoEvaluations.lean`. It contains only
the bookkeeping: the estimates themselves are hypotheses here.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional

open Filter Asymptotics MeasureTheory

noncomputable section

/-! ### The scales of [A] `eq:reflection-scales` -/

/-- `a = 9/10`: `X = Z^a`. -/
def signalExponentA : ℝ := 9 / 10

/-- `b = 133/1000`: `Y = Z^b`. -/
def signalExponentB : ℝ := 133 / 1000

/-- `M₀ = a + b = 1033/1000`: the rows have scale `XY = Z^{M₀}`. -/
def signalExponentM₀ : ℝ := 1033 / 1000

theorem signalExponentM₀_eq : signalExponentM₀ = signalExponentA + signalExponentB := by
  norm_num [signalExponentM₀, signalExponentA, signalExponentB]

/-- The exponent of the first evaluation: `(2M₀ - 1 - b)/2 = 933/2000`. -/
theorem reflection_exponent_eq :
    ((2 * signalExponentM₀ - 1) + -signalExponentB) / 2 = 933 / 2000 := by
  norm_num [signalExponentM₀, signalExponentB]

/-- `933/2000 = 7/15 - 1/6000`: the first row of [A] `tab:analytic-margins`. -/
theorem reflection_exponent_margin : (933 / 2000 : ℝ) = 7 / 15 - 1 / 6000 := by
  norm_num

/-! ### The first evaluation: Cauchy–Schwarz -/

/-- Cauchy–Schwarz for a paired series. -/
theorem norm_tsum_mul_le_sqrt_mul_sqrt {ι : Type*} (B W : ι → ℂ)
    (hB : Summable fun m => ‖B m‖ ^ 2) (hW : Summable fun m => ‖W m‖ ^ 2) :
    ‖∑' m, B m * W m‖ ≤ √(∑' m, ‖B m‖ ^ 2) * √(∑' m, ‖W m‖ ^ 2) := by
  have hB' : Summable fun m => ‖B m‖ ^ (2 : ℝ) := by simpa only [Real.rpow_two] using hB
  have hW' : Summable fun m => ‖W m‖ ^ (2 : ℝ) := by simpa only [Real.rpow_two] using hW
  obtain ⟨hsum, hle⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two (fun m => norm_nonneg (B m)) (fun m => norm_nonneg (W m)) hB' hW'
  have hnorm : Summable fun m => ‖B m * W m‖ := by simpa only [norm_mul] using hsum
  calc ‖∑' m, B m * W m‖ ≤ ∑' m, ‖B m * W m‖ := norm_tsum_le_tsum_norm hnorm
    _ = ∑' m, ‖B m‖ * ‖W m‖ := by simp only [norm_mul]
    _ ≤ (∑' m, ‖B m‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∑' m, ‖W m‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hle
    _ = √(∑' m, ‖B m‖ ^ 2) * √(∑' m, ‖W m‖ ^ 2) := by
      simp only [Real.rpow_two, Real.sqrt_eq_rpow]

/-- **[A]'s first evaluation from the two row masses** (`A-02a:0123–0136`). Let `I(Z)` be the
average over a finite measure space of the pairing `∑_m B_m(Z) W_m(Z)`. If, uniformly in the
average, `∑_m |B_m(Z)|² ≪_ε Z^{e_B + ε}` for every `ε > 0` and `∑_m |W_m(Z)|² ≪ Z^{e_W}`, then
`I(Z) ≪_ε Z^{(e_B + e_W)/2 + ε}` for every `ε > 0`. -/
theorem isBigO_of_secondMoments {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {B W : ℝ → Ω → ι → ℂ} {I : ℝ → ℂ} {eB eW : ℝ}
    (hI : ∀ᶠ Z in atTop, I Z = ∫ ω, ∑' m, B Z ω m * W Z ω m ∂μ)
    (hBsum : ∀ᶠ Z in atTop, ∀ ω, Summable fun m => ‖B Z ω m‖ ^ 2)
    (hWsum : ∀ᶠ Z in atTop, ∀ ω, Summable fun m => ‖W Z ω m‖ ^ 2)
    (hB : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ Z in atTop, ∀ ω,
      ∑' m, ‖B Z ω m‖ ^ 2 ≤ C * Z ^ (eB + ε))
    (hW : ∃ C : ℝ, ∀ᶠ Z in atTop, ∀ ω, ∑' m, ‖W Z ω m‖ ^ 2 ≤ C * Z ^ eW) :
    ∀ ε : ℝ, 0 < ε → I =O[atTop] fun Z : ℝ => Z ^ ((eB + eW) / 2 + ε) := by
  intro ε hε
  obtain ⟨CB, hCB⟩ := hB (2 * ε) (by positivity)
  obtain ⟨CW, hCW⟩ := hW
  refine IsBigO.of_bound (√(|CB| * |CW|) * μ.real Set.univ) ?_
  filter_upwards [hI, hBsum, hWsum, hCB, hCW, eventually_gt_atTop (0 : ℝ)] with
    Z hIZ hBs hWs hBZ hWZ hZ
  have hpow : Z ^ (eB + 2 * ε) * Z ^ eW = (Z ^ ((eB + eW) / 2 + ε)) ^ 2 := by
    rw [← Real.rpow_add hZ, ← Real.rpow_two, ← Real.rpow_mul hZ.le]
    congr 1
    ring
  have hpt : ∀ ω, ‖∑' m, B Z ω m * W Z ω m‖ ≤ √(|CB| * |CW|) * Z ^ ((eB + eW) / 2 + ε) := by
    intro ω
    have hB1 : ∑' m, ‖B Z ω m‖ ^ 2 ≤ |CB| * Z ^ (eB + 2 * ε) :=
      (hBZ ω).trans (mul_le_mul_of_nonneg_right (le_abs_self CB) (Real.rpow_nonneg hZ.le _))
    have hW1 : ∑' m, ‖W Z ω m‖ ^ 2 ≤ |CW| * Z ^ eW :=
      (hWZ ω).trans (mul_le_mul_of_nonneg_right (le_abs_self CW) (Real.rpow_nonneg hZ.le _))
    calc ‖∑' m, B Z ω m * W Z ω m‖
        ≤ √(∑' m, ‖B Z ω m‖ ^ 2) * √(∑' m, ‖W Z ω m‖ ^ 2) :=
          norm_tsum_mul_le_sqrt_mul_sqrt (B Z ω) (W Z ω) (hBs ω) (hWs ω)
      _ ≤ √(|CB| * Z ^ (eB + 2 * ε)) * √(|CW| * Z ^ eW) :=
          mul_le_mul (Real.sqrt_le_sqrt hB1) (Real.sqrt_le_sqrt hW1) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = √(|CB| * |CW|) * Z ^ ((eB + eW) / 2 + ε) := by
          have hnn : 0 ≤ |CB| * Z ^ (eB + 2 * ε) :=
            mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hZ.le _)
          rw [← Real.sqrt_mul hnn]
          have hrew : |CB| * Z ^ (eB + 2 * ε) * (|CW| * Z ^ eW) =
              |CB| * |CW| * (Z ^ ((eB + eW) / 2 + ε)) ^ 2 := by
            rw [← hpow]
            ring
          rw [hrew, Real.sqrt_mul (mul_nonneg (abs_nonneg _) (abs_nonneg _)),
            Real.sqrt_sq (Real.rpow_nonneg hZ.le _)]
  have hint := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hpt)
  rw [hIZ, Real.norm_of_nonneg (Real.rpow_nonneg hZ.le _)]
  calc ‖∫ ω, ∑' m, B Z ω m * W Z ω m ∂μ‖
      ≤ √(|CB| * |CW|) * Z ^ ((eB + eW) / 2 + ε) * μ.real Set.univ := hint
    _ = √(|CB| * |CW|) * μ.real Set.univ * Z ^ ((eB + eW) / 2 + ε) := by ring

/-! ### The second evaluation: [A] `tab:analytic-margins` -/

/-- [A] `tab:analytic-margins`: the margins below `7/15` of the six error terms of the Poisson
evaluation, in the order: principal remainder `R_w`, principal remainder `R_z`, nonprincipal rows
`U ≤ Z^{.09}`, exceptional rows `U ≤ Z^{.10001}`, good central rows `U ≤ Z^{.10001}`, rows
`U > Z^{.10001}`. The values are the exact rationals behind the decimals of the table. -/
def poissonMargin : Fin 6 → ℝ :=
  ![664989 / 100000000, 19997 / 30000000, 308027 / 30000000, 1477847 / 30000000,
    377 / 300000, 5297 / 300000]

/-- Every margin of the Poisson evaluation exceeds `5/10000`. -/
theorem poissonMargin_gt (j : Fin 6) : (5 / 10000 : ℝ) < poissonMargin j := by
  fin_cases j <;> simp [poissonMargin] <;> norm_num

/-- **[A]'s second evaluation from the six contributions** (`A-06:0648–0674`): if
`I(Z) - c₀ f(Z)` is a sum of six terms, each `≪_ε Z^{7/15 - margin + ε}` for every `ε > 0`, then
`I(Z) - c₀ f(Z) ≪ Z^{7/15 - 4/10000}`. -/
theorem isBigO_sub_of_poissonContributions {I f : ℝ → ℂ} {c₀ : ℂ} (E : Fin 6 → ℝ → ℂ)
    (hsplit : ∀ᶠ Z in atTop, I Z - c₀ * f Z = ∑ j, E j Z)
    (hE : ∀ j, ∀ ε : ℝ, 0 < ε →
      E j =O[atTop] fun Z : ℝ => Z ^ ((7 / 15 : ℝ) - poissonMargin j + ε)) :
    (fun Z => I Z - c₀ * f Z) =O[atTop] fun Z : ℝ => Z ^ ((7 / 15 : ℝ) - 4 / 10000) := by
  have hj : ∀ j, E j =O[atTop] fun Z : ℝ => Z ^ ((7 / 15 : ℝ) - 4 / 10000) := fun j =>
    (hE j (1 / 10000) (by norm_num)).trans
      (rpow_isBigO_rpow_atTop (by have := poissonMargin_gt j; linarith))
  have hsum : (fun Z => ∑ j, E j Z) =O[atTop] fun Z : ℝ => Z ^ ((7 / 15 : ℝ) - 4 / 10000) :=
    (IsBigO.sum (s := Finset.univ) fun j _ => hj j).congr_left fun Z =>
      Finset.sum_apply Z _ _
  exact hsum.congr' (hsplit.mono fun Z h => h.symm) EventuallyEq.rfl

/-! ### The two evaluations -/

/-- **[A] §2a from the section-level estimates.** The reflected second moment of the coefficient
sums `B`, the row mass of the additive factor `W`, and the six contributions `E` of the Poisson
evaluation give [A]'s two evaluations of the common signal against `f`. -/
theorem hasTwoEvaluations_of_sectionEstimates {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {B W : ℝ → Ω → ι → ℂ} {I f : ℝ → ℂ} {c₀ : ℂ} (hc₀ : c₀ ≠ 0)
    (hI : ∀ᶠ Z in atTop, I Z = ∫ ω, ∑' m, B Z ω m * W Z ω m ∂μ)
    (hBsum : ∀ᶠ Z in atTop, ∀ ω, Summable fun m => ‖B Z ω m‖ ^ 2)
    (hWsum : ∀ᶠ Z in atTop, ∀ ω, Summable fun m => ‖W Z ω m‖ ^ 2)
    (hB : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ Z in atTop, ∀ ω,
      ∑' m, ‖B Z ω m‖ ^ 2 ≤ C * Z ^ (2 * signalExponentM₀ - 1 + ε))
    (hW : ∃ C : ℝ, ∀ᶠ Z in atTop, ∀ ω, ∑' m, ‖W Z ω m‖ ^ 2 ≤ C * Z ^ (-signalExponentB))
    (E : Fin 6 → ℝ → ℂ) (hsplit : ∀ᶠ Z in atTop, I Z - c₀ * f Z = ∑ j, E j Z)
    (hE : ∀ j, ∀ ε : ℝ, 0 < ε →
      E j =O[atTop] fun Z : ℝ => Z ^ ((7 / 15 : ℝ) - poissonMargin j + ε)) :
    HasTwoEvaluations f := by
  refine ⟨I, c₀, hc₀, fun ε hε => ?_, isBigO_sub_of_poissonContributions E hsplit hE⟩
  have h := isBigO_of_secondMoments hI hBsum hWsum hB hW ε hε
  simpa only [reflection_exponent_eq] using h

end

end SimultaneousPrimitiveRoots.Unconditional
