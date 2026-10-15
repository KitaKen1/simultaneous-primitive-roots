module

public import SimultaneousPrimitiveRoots.Explicit.KummerZetaGRH

/-!
# The unconditional-route interface with continuation and growth discharged

The project's unconditional route reduces `MainClaim` to candidate supply and
`UniformKummerEntireGrowthGapInputs` for the zeta *quotients* (entire continuation, growth,
fixed-width zero gap). Running the finite-contour machinery on `F_K = (s - 1) ζ_K(s)` instead
(`Explicit/`), continuation and growth are theorems, and only the zero gap remains:

`mainClaim_of_supply_and_zetaGap`: candidate supply + a zero gap of width `δ > η` for the zeros of
`ζ_K` (`K = ℚ(ζ_q, a^{1/q})`, `q ∉ B` in the relevant range, height `≤ 2q²`) ⇒ `MainClaim`.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open Filter
noncomputable section

/-- A zero gap of width `δ` for the Dedekind zeta functions of the Kummer fields
`ℚ(ζ_q, a^{1/q})`, `a ∈ A`, uniformly for good primes `q ≤ 2 x^η`. -/
def UniformKummerZetaGap (A : Finset ℕ) (δ η : ℝ) (B : Set ℕ) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ a ∈ A, ∀ q : ℕ, ∀ ha : 2 ≤ a, ∀ hq : q.Prime,
    ∀ haq : a < q, q ∉ B → q ≤ Nat.floor (2 * x ^ η) →
    letI : Fact (2 ≤ a) := ⟨ha⟩
    letI : Fact q.Prime := ⟨hq⟩
    letI : Fact (a < q) := ⟨haq⟩
    ∀ i : fullQuotientZeroIndex (Hecke.dedekindZetaEntire (PrimeKummerField a q)),
      (fullQuotientIndexedZero _ i).im ≠ 0 →
      |(fullQuotientIndexedZero _ i).im| ≤ 2 * (q : ℝ) ^ 2 →
        (fullQuotientIndexedZero _ i).re ≤ 1 - δ

/-- The growth constant uniform over the bases in `A`. -/
def kummerZetaUniformGrowthConstant (A : Finset ℕ) : ℝ :=
  320 * (kummerDiscriminantConstant A + 1)

theorem kummerZetaUniformGrowthConstant_nonneg (A : Finset ℕ) :
    0 ≤ kummerZetaUniformGrowthConstant A := by
  unfold kummerZetaUniformGrowthConstant
  have := kummerDiscriminantConstant_nonneg A
  positivity

/-- The zero gap for `ζ_K` gives all the analytic inputs of the finite-contour machinery. -/
theorem uniformKummerEntireGrowthGapInputs_of_zetaGap {A : Finset ℕ} {δ η : ℝ} {B : Set ℕ}
    (h : UniformKummerZetaGap A δ η B) :
    UniformKummerEntireGrowthGapInputs A δ η (kummerZetaUniformGrowthConstant A) B := by
  filter_upwards [h] with x hx
  intro a haA q ha hq haq hgood hcut
  let : Fact (2 ≤ a) := ⟨ha⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (a < q) := ⟨haq⟩
  refine ⟨Hecke.dedekindZetaEntire (PrimeKummerField a q),
    dedekindZetaEntire_entireZeroData _ _, fun U hU z hz => ?_,
    hx a haA q ha hq haq hgood hcut⟩
  refine (Hecke.norm_dedekindZetaEntire_le_sphere _ hU hz).trans (Real.exp_le_exp.mpr ?_)
  have hc := Hecke.primeKummer_complexity_le_uniform A haA (a := a) (q := q)
  have hU3 : 0 ≤ (U + 3) ^ 2 := sq_nonneg _
  unfold kummerZetaUniformGrowthConstant
  calc 320 * ((Module.finrank ℚ (PrimeKummerField a q) : ℝ) +
        Real.log |((NumberField.discr (PrimeKummerField a q) : ℤ) : ℝ)|) * (U + 3) ^ 2
      ≤ 320 * ((kummerDiscriminantConstant A + 1) * ((q : ℝ) * ((q : ℝ) - 1)) *
          Real.log (2 * (q : ℝ))) * (U + 3) ^ 2 := by gcongr
    _ = _ := by ring

/-- **The unconditional-route closure for `ζ_K`.** Candidate supply and a zero gap of width
`δ > η` for the Dedekind zeta functions of the Kummer fields give `MainClaim`; continuation and
growth are proved. -/
theorem mainClaim_of_supply_and_zetaGap {δ η : ℝ}
    (hη : 0 ≤ η) (hηδ : η < δ) (hηfifth : η < 1 / 5) (hδ : δ ≤ 1)
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A η θ)
    (hgap : ∀ A : Finset ℕ, Admissible A → ∃ B : Set ℕ,
      Summable (badReciprocalWeight B) ∧ UniformKummerZetaGap A δ η B) : MainClaim := by
  apply mainClaim_of_entire_growth_gap hη hηδ hηfifth hδ hsupply
  intro A hA
  obtain ⟨B, hB, hg⟩ := hgap A hA
  exact ⟨kummerZetaUniformGrowthConstant A, B, kummerZetaUniformGrowthConstant_nonneg A, hB,
    uniformKummerEntireGrowthGapInputs_of_zetaGap hg⟩

end
end SimultaneousPrimitiveRoots.Explicit
