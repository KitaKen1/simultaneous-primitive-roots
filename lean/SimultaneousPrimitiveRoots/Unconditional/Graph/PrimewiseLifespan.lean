module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.PrimewiseExpectation
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

/-!
# Exact active lifespan coefficients

[S, §2, `eq:prefix-ghost`] and [P, §4]: after the common active color
is fixed, expand the damping before the first and after the last active
visit. The four endpoint cases preserve the ghost signs, include arbitrary
inactive visits between active runs, and pay the color cardinality once.
This does not yet identify complete memory histories or their operators.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

section Ring
variable {ι R : Type*} [LinearOrder ι] [CommRing R]

/-- Damping at inactive visits strictly inside the lifespan endpoints. -/
def lifespanDamping (s : Finset ι) (x : ι → R) (a z : ι) : R :=
  ∏ i ∈ s with a < i ∧ i < z, (1 - x i)

/-- Cutting an open interval at an active visit loses no inactive damping. -/
theorem lifespanDamping_split (s : Finset ι) (x : ι → R) {a b c : ι}
    (hab : a ≤ b) (hbc : b ≤ c) (hb : b ∉ s) :
    lifespanDamping s x a c = lifespanDamping s x a b * lifespanDamping s x b c := by
  classical
  have hs : s.filter (fun i => a < i ∧ i < c) =
      s.filter (fun i => a < i ∧ i < b) ∪ s.filter (fun i => b < i ∧ i < c) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hi, hai, hic⟩
      have hib : i ≠ b := fun h => hb (h ▸ hi)
      rcases lt_or_gt_of_ne hib with h | h
      · exact Or.inl ⟨hi, hai, h⟩
      · exact Or.inr ⟨hi, h, hic⟩
    · rintro (⟨hi, hai, hib⟩ | ⟨hi, hbi, hic⟩)
      · exact ⟨hi, hai, hib.trans_le hbc⟩
      · exact ⟨hi, hab.trans_lt hbi, hic⟩
  have hd : Disjoint (s.filter (fun i => a < i ∧ i < b))
      (s.filter (fun i => b < i ∧ i < c)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have h₁ := (Finset.mem_filter.mp hi).2.2
    have h₂ := (Finset.mem_filter.mp hj).2.1
    order
  unfold lifespanDamping
  rw [hs, Finset.prod_union hd]

/-- Partition inactive visits before, inside and after the active interval. -/
theorem damping_product_interval_split (s : Finset ι) (x : ι → R) {a z : ι}
    (haz : a ≤ z) (ha : a ∉ s) (hz : z ∉ s) :
    (∏ i ∈ s, (1 - x i)) = (∏ i ∈ s with i < a, (1 - x i)) *
      lifespanDamping s x a z * (∏ i ∈ s with z < i, (1 - x i)) := by
  classical
  have hs : s = (s.filter (fun i => i < a) ∪
      s.filter (fun i => a < i ∧ i < z)) ∪ s.filter (fun i => z < i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      have hiz : i ≠ z := fun h => hz (h ▸ hi)
      rcases lt_or_gt_of_ne hia with h | h
      · exact Or.inl (Or.inl ⟨hi, h⟩)
      · rcases lt_or_gt_of_ne hiz with h' | h'
        · exact Or.inl (Or.inr ⟨hi, h, h'⟩)
        · exact Or.inr ⟨hi, h'⟩
    · rintro ((⟨hi, _⟩ | ⟨hi, _⟩) | ⟨hi, _⟩) <;> exact hi
  have hd₁ : Disjoint (s.filter (fun i => i < a))
      (s.filter (fun i => a < i ∧ i < z)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have h₁ := (Finset.mem_filter.mp hi).2
    have h₂ := (Finset.mem_filter.mp hj).2.1
    order
  have hd₂ : Disjoint (s.filter (fun i => i < a) ∪
      s.filter (fun i => a < i ∧ i < z)) (s.filter (fun i => z < i)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have h₂ := (Finset.mem_filter.mp hj).2
    rcases Finset.mem_union.mp hi with hi | hi
    · have h₁ := (Finset.mem_filter.mp hi).2
      order
    · have h₁ := (Finset.mem_filter.mp hi).2.2
      order
  calc
    _ = ∏ i ∈ ((s.filter (fun i => i < a) ∪
        s.filter (fun i => a < i ∧ i < z)) ∪ s.filter (fun i => z < i)),
          (1 - x i) := Finset.prod_congr hs fun _ _ => rfl
    _ = _ := by rw [Finset.prod_union hd₂, Finset.prod_union hd₁]; rfl

/-- Factorized endpoint choices, including the choice of no ghost endpoint. -/
theorem damping_product_lifespan_factors (s : Finset ι) (x : ι → R) {a z : ι}
    (haz : a ≤ z) (ha : a ∉ s) (hz : z ∉ s) :
    (∏ i ∈ s, (1 - x i)) =
      (1 - ∑ j ∈ s with j < a, x j * lifespanDamping s x j a) *
        lifespanDamping s x a z *
      (1 - ∑ k ∈ s with z < k, x k * lifespanDamping s x z k) := by
  have hp : (∏ i ∈ s with i < a, (1 - x i)) =
      1 - ∑ j ∈ s with j < a, x j * lifespanDamping s x j a := by
    simpa only [lifespanDamping, Finset.filter_filter, and_comm] using
      damping_product_last (s.filter (fun i => i < a)) x
  have hq : (∏ i ∈ s with z < i, (1 - x i)) =
      1 - ∑ k ∈ s with z < k, x k * lifespanDamping s x z k := by
    simpa only [lifespanDamping, Finset.filter_filter] using
      damping_product_first (s.filter (fun i => z < i)) x
  rw [damping_product_interval_split s x haz ha hz, hp, hq]

/-- Exact four-case active lifespan expansion: neither ghost, birth only,
termination only, or both ghosts. The two negative endpoint signs multiply. -/
theorem damping_product_lifespans (s : Finset ι) (x : ι → R) {a z : ι}
    (haz : a ≤ z) (ha : a ∉ s) (hz : z ∉ s) :
    (∏ i ∈ s, (1 - x i)) = lifespanDamping s x a z -
      (∑ j ∈ s with j < a, x j * lifespanDamping s x j z) -
      (∑ k ∈ s with z < k, x k * lifespanDamping s x a k) +
      ∑ j ∈ s with j < a, ∑ k ∈ s with z < k,
        x j * x k * lifespanDamping s x j k := by
  classical
  let A := ∑ j ∈ s with j < a, x j * lifespanDamping s x j a
  let B := ∑ k ∈ s with z < k, x k * lifespanDamping s x z k
  let D := lifespanDamping s x a z
  have hA : A * D = ∑ j ∈ s with j < a, x j * lifespanDamping s x j z := by
    dsimp [A, D]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [lifespanDamping_split s x (Finset.mem_filter.mp hj).2.le haz ha]
    ring
  have hB : D * B = ∑ k ∈ s with z < k, x k * lifespanDamping s x a k := by
    dsimp [B, D]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [lifespanDamping_split s x haz (Finset.mem_filter.mp hk).2.le hz]
    ring
  have hAB : A * D * B = ∑ j ∈ s with j < a, ∑ k ∈ s with z < k,
      x j * x k * lifespanDamping s x j k := by
    dsimp [A, B, D]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hja := (Finset.mem_filter.mp hj).2.le
    have hzk := (Finset.mem_filter.mp hk).2.le
    rw [lifespanDamping_split s x (hja.trans haz) hzk hz,
      lifespanDamping_split s x hja haz ha]
    ring
  calc
    _ = (1 - A) * D * (1 - B) := damping_product_lifespan_factors s x haz ha hz
    _ = D - A * D - D * B + A * D * B := by ring
    _ = _ := by rw [hAB, hA, hB]

end Ring

section Field
variable {ι C K : Type*} [LinearOrder ι] [Fintype C] [DecidableEq C]
  [Field K] [CharZero K]

/-- Expand a compatible active prime with the actual first/last active visits.
All inactive visits between active runs stay in the same lifespan product. -/
theorem primewise_active_lifespan_expectation
    (s active : Finset ι) (color : ι → C) (η : ι → K) (c₀ : C) {a z : ι}
    (ha : a ∈ active) (hz : z ∈ active)
    (hspan : ∀ i ∈ active, a ≤ i ∧ i ≤ z)
    (hcolor : ∀ i ∈ active, color i = c₀) :
    (𝔼 c : C, (∏ i ∈ active, if color i = c then (1 : K) else 0) *
      ∏ i ∈ s \ active, (1 - hitWeight color η i c)) =
      (lifespanDamping (s \ active) (fun i => hitWeight color η i c₀) a z -
        (∑ j ∈ s \ active with j < a,
          hitWeight color η j c₀ * lifespanDamping (s \ active)
            (fun i => hitWeight color η i c₀) j z) -
        (∑ k ∈ s \ active with z < k,
          hitWeight color η k c₀ * lifespanDamping (s \ active)
            (fun i => hitWeight color η i c₀) a k) +
        ∑ j ∈ s \ active with j < a, ∑ k ∈ s \ active with z < k,
          hitWeight color η j c₀ * hitWeight color η k c₀ *
            lifespanDamping (s \ active) (fun i => hitWeight color η i c₀) j k) /
        (Fintype.card C : K) := by
  rw [primewise_active_expectation active (s \ active) color η c₀
    (show active.Nonempty from ⟨a, ha⟩) hcolor]
  rw [damping_product_lifespans (s \ active) (fun i => hitWeight color η i c₀)
    (hspan z hz).1 (by simp [ha]) (by simp [hz])]

end Field

end SimultaneousPrimitiveRoots.Unconditional.Graph
