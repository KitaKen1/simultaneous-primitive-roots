module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.PrimewiseMemory
public import Mathlib.Algebra.BigOperators.Expect

/-!
# Uniform primewise expectations

The orphan and active-color formulas use Mathlib's uniform finite expectation.
The sampled color is shared by all visits. In particular, a compatible
nonempty active set costs one reciprocal cardinality, regardless of its size.
These identities do not assert independence between visits or between primes.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {ι C K : Type*} [LinearOrder ι] [Fintype C] [DecidableEq C]
  [Field K] [CharZero K]

/-- The exact orphan expansion for a uniform color sampled once. -/
theorem primewise_orphan_expectation [Nonempty C]
    (s : Finset ι) (color : ι → C) (η : ι → K) :
    (𝔼 c : C, ∏ i ∈ s, (1 - hitWeight color η i c)) =
      1 - (∑ i ∈ s, η i) / (Fintype.card C : K) +
        (∑ z ∈ s, ∑ a ∈ s with a < z,
          if color a = color z then
            η a * η z * ∏ j ∈ s with a < j ∧ j < z,
              (1 - hitWeight color η j (color a))
          else 0) / (Fintype.card C : K) := by
  have hc : (Fintype.card C : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Fintype.expect_eq_sum_div_card, color_sum_orphans, add_div, sub_div, div_self hc]

omit [LinearOrder ι] in
/-- Two distinct active colors make the uniform expectation vanish. -/
theorem primewise_active_expectation_eq_zero
    (active inactive : Finset ι) (color : ι → C) (η : ι → K)
    {a b : ι} (ha : a ∈ active) (hb : b ∈ active) (hab : color a ≠ color b) :
    (𝔼 c : C, (∏ i ∈ active, if color i = c then (1 : K) else 0) *
      ∏ i ∈ inactive, (1 - hitWeight color η i c)) = 0 := by
  rw [Fintype.expect_eq_sum_div_card, active_color_sum_eq_zero active inactive color η ha hb hab,
    zero_div]

omit [LinearOrder ι] in
/-- A compatible nonempty active set costs exactly one reciprocal cardinality. -/
theorem primewise_active_expectation
    (active inactive : Finset ι) (color : ι → C) (η : ι → K) (c₀ : C)
    (hne : active.Nonempty) (hcolor : ∀ i ∈ active, color i = c₀) :
    (𝔼 c : C, (∏ i ∈ active, if color i = c then (1 : K) else 0) *
      ∏ i ∈ inactive, (1 - hitWeight color η i c)) =
      (∏ i ∈ inactive, (1 - hitWeight color η i c₀)) / (Fintype.card C : K) := by
  rw [Fintype.expect_eq_sum_div_card, active_color_sum active inactive color η c₀ hne hcolor]

end SimultaneousPrimitiveRoots.Unconditional.Graph
