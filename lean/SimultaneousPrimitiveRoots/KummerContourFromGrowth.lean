module

public import SimultaneousPrimitiveRoots.KummerGaussianLeftAverage

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Metric Filter
open scoped Topology
noncomputable section

/-- The remaining actual analytic data have no contour-remainder input. -/
def KummerEntireGrowthGapInputs (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (δ C : ℝ) : Prop :=
  ∃ H : ℂ → ℂ,
    NumberFieldEntireFullQuotientContinuation (PrimeKummerField a q) (CyclotomicField q ℚ) H ∧
    (∀ U : ℝ, 0 ≤ U → ∀ z ∈ sphere (2 : ℂ) (2 * (U + 2)),
      ‖H z‖ ≤ Real.exp
        (C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) * (U + 3) ^ 2)) ∧
    (∀ i : fullQuotientZeroIndex H, (fullQuotientIndexedZero H i).im ≠ 0 →
      |(fullQuotientIndexedZero H i).im| ≤ 2 * (q : ℝ) ^ 2 →
        (fullQuotientIndexedZero H i).re ≤ 1 - δ)

def UniformKummerEntireGrowthGapInputs (A : Finset ℕ) (δ η C : ℝ) (B : Set ℕ) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ a ∈ A, ∀ q : ℕ, ∀ ha : 2 ≤ a, ∀ hq : q.Prime,
    ∀ haq : a < q, q ∉ B → q ≤ Nat.floor (2 * x ^ η) →
    letI : Fact (2 ≤ a) := ⟨ha⟩
    letI : Fact q.Prime := ⟨hq⟩
    letI : Fact (a < q) := ⟨haq⟩
    KummerEntireGrowthGapInputs a q δ C

theorem kummerFiniteContourUpperInputs_of_boundary_growth {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {x δ C : ℝ}
    (hx : 1 ≤ x) (hC : 0 ≤ C) (hi : KummerEntireGrowthGapInputs a q δ C) :
    KummerFiniteContourUpperInputs a q x δ C (kummerGaussianLeftAverageConstant C + 1) := by
  obtain ⟨H, hH, hb, hg⟩ := hi
  exact kummerFiniteContourUpperInputs_of_left_edge hx hC
    ⟨H, hH, hb, hg, kummerGaussianLeftEdgeUpperInput_of_boundary_growth hH hC hx hb⟩

theorem uniformKummerFiniteContourUpperInputs_of_boundary_growth
    {A : Finset ℕ} {δ η C : ℝ} {B : Set ℕ} (hC : 0 ≤ C)
    (hi : UniformKummerEntireGrowthGapInputs A δ η C B) :
    UniformKummerFiniteContourUpperInputs A δ η C (kummerGaussianLeftAverageConstant C + 1) B := by
  filter_upwards [hi, eventually_ge_atTop (1 : ℝ)] with x hix hx
  intro a ha q ha2 hq haq hgood hcut
  let : Fact (2 ≤ a) := ⟨ha2⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (a < q) := ⟨haq⟩
  exact kummerFiniteContourUpperInputs_of_boundary_growth hx hC
    (hix a ha q ha2 hq haq hgood hcut)

theorem exists_gaussianFullLargeGoodTraceBound_of_entire_growth_gap
    (A : Finset ℕ) {δ η C : ℝ} {B : Set ℕ}
    (hη : η < 1 / 5) (hδ : δ ≤ 1) (hC : 0 ≤ C)
    (hi : UniformKummerEntireGrowthGapInputs A δ η C B) :
    ∃ D : ℝ, 0 ≤ D ∧ GaussianFullLargeGoodTraceBound A δ η D B (fun _ => 0) := by
  have hR : 0 ≤ kummerGaussianLeftAverageConstant C + 1 := by
    linarith [kummerGaussianLeftAverageConstant_nonneg hC]
  exact exists_gaussianFullLargeGoodTraceBound_of_finite_contours A hη hδ hC hR
    (uniformKummerFiniteContourUpperInputs_of_boundary_growth hC hi)

/-- Conditional main closure with the whole contour remainder derived. Actual
entire/growth/gap data, KR and candidate supply still need construction. -/
theorem mainClaim_of_entire_growth_gap {δ η : ℝ}
    (hη : 0 ≤ η) (hηδ : η < δ) (hηfifth : η < 1 / 5) (hδ : δ ≤ 1)
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A η θ)
    (hi : ∀ A : Finset ℕ, Admissible A → ∃ C : ℝ, ∃ B : Set ℕ,
      0 ≤ C ∧ Summable (badReciprocalWeight B) ∧
        UniformKummerEntireGrowthGapInputs A δ η C B) : MainClaim := by
  apply mainClaim_of_finite_contour_inputs hη hηδ hηfifth hδ hsupply
  intro A hA
  obtain ⟨C, B, hC, hB, hdata⟩ := hi A hA
  refine ⟨C, kummerGaussianLeftAverageConstant C + 1, B, hC, ?_, hB,
    uniformKummerFiniteContourUpperInputs_of_boundary_growth hC hdata⟩
  linarith [kummerGaussianLeftAverageConstant_nonneg hC]

end
end SimultaneousPrimitiveRoots
