module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring

/-!
# Exact primewise lifespan identities

The finite algebra in [P, §4, `mem:orphan-identity`, `mem:prefix`, `mem:suffix`]
and [S, §2, `eq:orphan-expansion`, `eq:prefix-ghost`]. Visits are any finite
subset of a linearly ordered type; colors are residue classes or projective
lines. Endpoint and interior damping may differ. No positivity, independence
between visits, or exclusion of repeated colors is assumed.

These are exact identities for one prime. They do not construct the complete
memory operators, prove their norms, or transfer to physical averages.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {ι R : Type*} [LinearOrder ι] [CommRing R]

/-- Telescoping towards earlier visits (the suffix ghost expansion). -/
theorem damping_product_first (s : Finset ι) (x : ι → R) :
    (∏ i ∈ s, (1 - x i)) =
      1 - ∑ i ∈ s, x i * ∏ j ∈ s with j < i, (1 - x j) :=
  Finset.prod_one_sub_ordered s x

/-- Telescoping towards later visits (the prefix ghost expansion). -/
theorem damping_product_last (s : Finset ι) (x : ι → R) :
    (∏ i ∈ s, (1 - x i)) =
      1 - ∑ i ∈ s, x i * ∏ j ∈ s with i < j, (1 - x j) :=
  Finset.prod_one_sub_ordered (ι := ιᵒᵈ) s x

/-- Group every term of degree at least two by its first and last visit.
The internal product sums all optional internal hits, with their signs. -/
theorem damping_product_orphans (s : Finset ι) (x : ι → R) :
    (∏ i ∈ s, (1 - x i)) = 1 - (∑ i ∈ s, x i) +
      ∑ c ∈ s, ∑ a ∈ s with a < c,
        x a * x c * ∏ j ∈ s with a < j ∧ j < c, (1 - x j) := by
  classical
  have hinner (c : ι) :
      x c * (∏ j ∈ s with j < c, (1 - x j)) = x c -
        ∑ a ∈ s with a < c,
          x a * x c * ∏ j ∈ s with a < j ∧ j < c, (1 - x j) := by
    rw [damping_product_last, mul_sub, mul_one, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Finset.filter_filter, and_comm]
    ring
  rw [damping_product_first]
  simp_rw [hinner]
  rw [Finset.sum_sub_distrib]
  ring

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- A damped hit on one color, written without a real-valued indicator. -/
def hitWeight (color : ι → C) (η : ι → R) (i : ι) (c : C) : R :=
  if color i = c then η i else 0

/-- A color is sampled once. The empty and singleton terms form the baseline;
every other term has exactly one pair of ghost endpoints. This is the raw
sum version of [P]'s projective-line and [S]'s residue expectation. -/
theorem color_sum_orphans (s : Finset ι) (color : ι → C) (η : ι → R) :
    (∑ c : C, ∏ i ∈ s, (1 - hitWeight color η i c)) =
      (Fintype.card C : R) - (∑ i ∈ s, η i) +
        ∑ z ∈ s, ∑ a ∈ s with a < z,
          if color a = color z then
            η a * η z * ∏ j ∈ s with a < j ∧ j < z,
              (1 - hitWeight color η j (color a))
          else 0 := by
  classical
  have hsingle (i : ι) : (∑ c : C, hitWeight color η i c) = η i := by
    simp [hitWeight]
  have hpair (a z : ι) :
      (∑ c : C, hitWeight color η a c * hitWeight color η z c *
        ∏ j ∈ s with a < j ∧ j < z, (1 - hitWeight color η j c)) =
      if color a = color z then
        η a * η z * ∏ j ∈ s with a < j ∧ j < z,
          (1 - hitWeight color η j (color a))
      else 0 := by
    rw [Finset.sum_eq_single (color a)]
    · by_cases h : color a = color z <;> simp [hitWeight, h, eq_comm]
    · intro c hc hca
      simp [hitWeight, hca.symm]
    · simp
  conv_lhs =>
    arg 2
    ext c
    rw [damping_product_orphans]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun c i => hitWeight color η i c)]
  simp_rw [hsingle]
  congr 1
  · simp
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z hz
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a ha => hpair a z

omit [LinearOrder ι] in
/-- Incompatible active colors contribute zero, before any damping. -/
theorem active_color_sum_eq_zero (active inactive : Finset ι) (color : ι → C)
    (η : ι → R) {a b : ι} (ha : a ∈ active) (hb : b ∈ active)
    (hab : color a ≠ color b) :
    (∑ c : C, (∏ i ∈ active, if color i = c then (1 : R) else 0) *
      ∏ i ∈ inactive, (1 - hitWeight color η i c)) = 0 := by
  apply Finset.sum_eq_zero
  intro c hc
  have hzero : (∏ i ∈ active, if color i = c then (1 : R) else 0) = 0 := by
    by_cases hac : color a = c
    · apply Finset.prod_eq_zero hb
      simp [show color b ≠ c from fun hbc => hab (hac.trans hbc.symm)]
    · apply Finset.prod_eq_zero ha
      simp [hac]
  rw [hzero, zero_mul]

omit [LinearOrder ι] in
/-- Compatible nonempty active visits fix a single color. The inverse color
cardinality in a uniform expectation is consequently paid only once. -/
theorem active_color_sum (active inactive : Finset ι) (color : ι → C)
    (η : ι → R) (c₀ : C) (hne : active.Nonempty)
    (hcolor : ∀ i ∈ active, color i = c₀) :
    (∑ c : C, (∏ i ∈ active, if color i = c then (1 : R) else 0) *
      ∏ i ∈ inactive, (1 - hitWeight color η i c)) =
      ∏ i ∈ inactive, (1 - hitWeight color η i c₀) := by
  classical
  rw [Finset.sum_eq_single c₀]
  · have hone : (∏ i ∈ active, if color i = c₀ then (1 : R) else 0) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      simp [hcolor i hi]
    rw [hone, one_mul]
  · intro c hc hcc
    obtain ⟨a, ha⟩ := hne
    have hzero : (∏ i ∈ active, if color i = c then (1 : R) else 0) = 0 := by
      apply Finset.prod_eq_zero ha
      simp [hcolor a ha, hcc.symm]
    rw [hzero, zero_mul]
  · simp

end SimultaneousPrimitiveRoots.Unconditional.Graph
