module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.HighRank.Blocks
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Large rank: fresh integrations with prescribed prime values

Source: `verification/stage7-sources/S-02.tex`, lines 1127–1136 (`[S-02:1127–1136]`).

"In the proof of Lemma 3.8, replace the total fresh mass in each constrained slot by its
single-point bound. For a ghost operation keep its ordered batch integral and factorial divisor;
constraining indicated fresh coordinates replaces their mass factors by the same single-point
bound. … Initial active slots satisfy the same product estimate."

All births of the memory evolution are integrated against the tilted laws `μ̃_g`: the labels of
the initial big list, the fresh target labels of an edge, and the coordinates of an ordered ghost
batch. This file computes these product integrals when some coordinates are pinned to prescribed
natural numbers.

* `hrPtMass 𝒢 q n g z` — the point mass of `μ̃_g` at the natural number `z` (zero outside `𝒫_g`,
  in particular at a prime of another group).
* `hr_sum_pin_le` — one coordinate: a pinned coordinate contributes its point mass, a free one the
  total mass.
* `hr_sum_labelList_le` — a list of labels (the big active list; the fresh target slots `F` of an
  edge, the other slots being fixed).
* `hrBatchBirth`, `hr_sum_batch_le` — an ordered ghost batch of a given size: the sum over the
  batches with the prescribed coordinates is at most the product of the point masses times the sum
  over all batches (here `μ̃_g(𝒫_g) ≥ 1` is used).
* `hr_one_le_tilt_sum` — `μ̃_g(𝒫_g) ≥ 1` when `0 < b_p ≤ 1`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Point masses -/

section HrPoint

variable {S B : Type} {𝒢 : GroupFamily S B}

/-- **The point mass of `μ̃_g` at the natural number `z`**: `μ̃_g(z)` if `z ∈ 𝒫_g` and `0`
otherwise; `sup_{g, p} μ̃_g(p) ≪ P_*^{-1}` is (eq:tilted-point-mass) [S-02:1114–1117]. -/
def hrPtMass (𝒢 : GroupFamily S B) (q : ℝ) (n : ℕ) (g : B) (z : ℕ) : ℝ :=
  if z ∈ 𝒢.big g then tiltLaw (𝒢.big g) q n z else 0

theorem hrPtMass_nonneg {q : ℝ} {n : ℕ} {g : B}
    (hν : ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p) (z : ℕ) : 0 ≤ hrPtMass 𝒢 q n g z := by
  unfold hrPtMass
  split_ifs with h
  · exact hν z h
  · exact le_rfl

theorem hrPtMass_le {q : ℝ} {n : ℕ} {g : B} {μ : ℝ}
    (hμ : ∀ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) q n p ≤ μ) (hμ0 : 0 ≤ μ) (z : ℕ) :
    hrPtMass 𝒢 q n g z ≤ μ := by
  unfold hrPtMass
  split_ifs with h
  · exact hμ z h
  · exact hμ0

/-- The total of the point masses over a set of values which contains the group. -/
theorem hr_sum_ptMass (q : ℝ) (n : ℕ) (g : B) {V : Finset ℕ} (hV : 𝒢.big g ⊆ V) :
    ∑ z ∈ V, hrPtMass 𝒢 q n g z = ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) q n p := by
  unfold hrPtMass
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hV]

open _root_.Classical in
/-- **The integration of one coordinate**: if the value of the coordinate is prescribed, the
integral of `μ̃_g` is the point mass; otherwise it is the total mass. Both are at most
`hrW (point mass) · M₁` for every `M₁ ≥ max(1, μ̃_g(𝒫_g))`. -/
theorem hr_sum_pin_le {q : ℝ} {n : ℕ} {g : B} {M1 : ℝ}
    (hν : ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p)
    (hM : ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) q n p ≤ M1) (h1 : 1 ≤ M1) (o : Option ℕ) :
    ∑ p : {p : ℕ // p ∈ 𝒢.big g},
        (if ∀ z, o = some z → (p : ℕ) = z then tiltLaw (𝒢.big g) q n p else 0) ≤
      hrW (hrPtMass 𝒢 q n g) o * M1 := by
  cases o with
  | none =>
    rw [hrW_none, one_mul]
    refine le_trans (le_of_eq ?_) hM
    rw [← Finset.sum_coe_sort (𝒢.big g) fun p => tiltLaw (𝒢.big g) q n p]
    refine Finset.sum_congr rfl fun p _ => ?_
    exact if_pos fun z hz => absurd hz (Option.some_ne_none z).symm
  | some z₀ =>
    rw [hrW_some]
    have hcond : ∀ p : {p : ℕ // p ∈ 𝒢.big g},
        (∀ z, some z₀ = some z → (p : ℕ) = z) ↔ (p : ℕ) = z₀ :=
      fun p => ⟨fun h => h z₀ rfl, fun h z hz => h.trans (Option.some.inj hz)⟩
    have hsum : ∑ p : {p : ℕ // p ∈ 𝒢.big g},
        (if ∀ z, some z₀ = some z → (p : ℕ) = z then tiltLaw (𝒢.big g) q n p else 0) =
          hrPtMass 𝒢 q n g z₀ := by
      unfold hrPtMass
      by_cases hz : z₀ ∈ 𝒢.big g
      · rw [if_pos hz,
          Finset.sum_eq_single_of_mem (⟨z₀, hz⟩ : {p : ℕ // p ∈ 𝒢.big g}) (Finset.mem_univ _)]
        · exact if_pos ((hcond _).mpr rfl)
        · intro p _ hp
          exact if_neg fun h => hp (Subtype.ext ((hcond p).mp h))
      · rw [if_neg hz]
        refine Finset.sum_eq_zero fun p _ => ?_
        exact if_neg fun h => hz (((hcond p).mp h) ▸ p.2)
    rw [hsum]
    exact le_mul_of_one_le_right (hrPtMass_nonneg hν z₀) h1

/-- `μ_g(p) ≤ μ̃_g(p)` when `0 < b_p ≤ 1` (eq:lifespan-baseline). -/
theorem hr_law_le_tiltLaw (s : Finset ℕ) (q : ℝ) (n p : ℕ)
    (hV : 0 < Graph.primeGroupReciprocalMass s) (hp : 0 < p) (hb : 0 < lifeBaseline q n p)
    (hb1 : lifeBaseline q n p ≤ 1) : Graph.primeGroupLaw s p ≤ tiltLaw s q n p := by
  have hVp : 0 < Graph.primeGroupReciprocalMass s * (p : ℝ) := mul_pos hV (Nat.cast_pos.mpr hp)
  have hden : 0 < Graph.primeGroupReciprocalMass s * (p : ℝ) * lifeBaseline q n p :=
    mul_pos hVp hb
  have hle : Graph.primeGroupReciprocalMass s * (p : ℝ) * lifeBaseline q n p ≤
      Graph.primeGroupReciprocalMass s * (p : ℝ) := mul_le_of_le_one_right hVp.le hb1
  exact one_div_le_one_div_of_le hden hle

/-- **`μ̃_g(𝒫_g) ≥ 1`** when `0 < b_p ≤ 1` on the group: the tilted law dominates the probability
law `μ_g`. -/
theorem hr_one_le_tilt_sum (s : Finset ℕ) (q : ℝ) (n : ℕ)
    (hV : 0 < Graph.primeGroupReciprocalMass s) (hpos : ∀ p ∈ s, 0 < p)
    (hlaw : ∑ p ∈ s, Graph.primeGroupLaw s p = 1) (hb : ∀ p ∈ s, 0 < lifeBaseline q n p)
    (hb1 : ∀ p ∈ s, lifeBaseline q n p ≤ 1) : 1 ≤ ∑ p ∈ s, tiltLaw s q n p := by
  rw [← hlaw]
  exact Finset.sum_le_sum fun p hp =>
    hr_law_le_tiltLaw s q n p hV (hpos p hp) (hb p hp) (hb1 p hp)

end HrPoint

/-! ### Lists of labels -/

section HrLists

variable {S B : Type} [Fintype B] [DecidableEq B] {J ℓ : ℕ}

open _root_.Classical in
/-- **The integral over the labels of the slots of `F`, with prescribed values** [S-02:1127–1129]:
the sum over the lists `x` which agree with `x₀` outside `F` and in which every slot with a
prescribed value belongs to `F` and carries that value, of `∏_{g, sl ∈ F_g} μ̃_g(x_{g,sl})`, is at
most the product of the point masses of the prescribed values times `M₁^{|F_g|}`,
`M₁ ≥ max(1, μ̃_g(𝒫_g))`. -/
theorem hr_sum_labelList_le (𝒢 : GroupFamily S B) {q : ℝ} {n : ℕ} {M1 : ℝ}
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p)
    (hM : ∀ g, ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) q n p ≤ M1) (h1 : 1 ≤ M1)
    (F : (g : B) → Finset (Slot J ℓ)) (x₀ : LabelList 𝒢.big J ℓ)
    (pv : (g : B) → Slot J ℓ → Option ℕ) :
    ∑ x : LabelList 𝒢.big J ℓ,
        (if (∀ g sl, sl ∉ F g → x g sl = x₀ g sl) ∧
            (∀ g sl z, pv g sl = some z → sl ∈ F g ∧ (x g sl : ℕ) = z) then
          ∏ g, ∏ sl ∈ F g, tiltLaw (𝒢.big g) q n (x g sl)
        else 0) ≤
      (∏ g, ∏ sl, hrW (hrPtMass 𝒢 q n g) (pv g sl)) * ∏ g, M1 ^ (F g).card := by
  have hM0 : 0 ≤ M1 := zero_le_one.trans h1
  have hW0 : ∀ g sl, 0 ≤ hrW (hrPtMass 𝒢 q n g) (pv g sl) := fun g sl =>
    hrW_nonneg (hrPtMass_nonneg (hν g)) _
  have hRHS : 0 ≤ (∏ g, ∏ sl, hrW (hrPtMass 𝒢 q n g) (pv g sl)) * ∏ g, M1 ^ (F g).card :=
    mul_nonneg (Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun sl _ => hW0 g sl)
      (Finset.prod_nonneg fun g _ => pow_nonneg hM0 _)
  by_cases hsub : ∀ g sl z, pv g sl = some z → sl ∈ F g
  · -- the weights of the labels of one slot
    obtain ⟨ω, hω⟩ : ∃ ω : (g : B) → Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g} → ℝ, ∀ g sl p,
        ω g sl p = if sl ∈ F g then
          (if ∀ z, pv g sl = some z → (p : ℕ) = z then tiltLaw (𝒢.big g) q n p else 0)
          else (if p = x₀ g sl then 1 else 0) := ⟨_, fun _ _ _ => rfl⟩
    have hω0 : ∀ g sl p, 0 ≤ ω g sl p := by
      intro g sl p
      rw [hω]
      split_ifs
      · exact hν g _ p.2
      · exact le_rfl
      · exact zero_le_one
      · exact le_rfl
    -- one term of the integral
    have hterm : ∀ x : LabelList 𝒢.big J ℓ,
        (if (∀ g sl, sl ∉ F g → x g sl = x₀ g sl) ∧
            (∀ g sl z, pv g sl = some z → sl ∈ F g ∧ (x g sl : ℕ) = z) then
          ∏ g, ∏ sl ∈ F g, tiltLaw (𝒢.big g) q n (x g sl)
        else 0) ≤ ∏ g, ∏ sl, ω g sl (x g sl) := by
      intro x
      have hnn : 0 ≤ ∏ g, ∏ sl, ω g sl (x g sl) :=
        Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun sl _ => hω0 g sl _
      by_cases hc : (∀ g sl, sl ∉ F g → x g sl = x₀ g sl) ∧
          (∀ g sl z, pv g sl = some z → sl ∈ F g ∧ (x g sl : ℕ) = z)
      · rw [if_pos hc]
        refine le_of_eq (Finset.prod_congr rfl fun g _ => ?_)
        have h2 : ∀ sl : Slot J ℓ, ω g sl (x g sl) =
            if sl ∈ F g then tiltLaw (𝒢.big g) q n (x g sl) else 1 := by
          intro sl
          rw [hω]
          by_cases hsl : sl ∈ F g
          · rw [if_pos hsl, if_pos hsl]
            exact if_pos fun z hz => (hc.2 g sl z hz).2
          · rw [if_neg hsl, if_neg hsl]
            exact if_pos (hc.1 g sl hsl)
        rw [Finset.prod_congr rfl fun sl _ => h2 sl, Finset.prod_ite_mem, Finset.univ_inter]
      · rw [if_neg hc]
        exact hnn
    -- the sum of the weights of the labels of one slot
    have hslot : ∀ g sl, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, ω g sl p ≤
        hrW (hrPtMass 𝒢 q n g) (pv g sl) * (if sl ∈ F g then M1 else 1) := by
      intro g sl
      by_cases hsl : sl ∈ F g
      · rw [if_pos hsl]
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
          (hr_sum_pin_le (hν g) (hM g) h1 (pv g sl))
        rw [hω, if_pos hsl]
      · have hnone : pv g sl = none := by
          cases hp : pv g sl with
          | none => rfl
          | some z => exact absurd (hsub g sl z hp) hsl
        rw [if_neg hsl, hnone, hrW_none, one_mul]
        have h2 : ∑ p : {p : ℕ // p ∈ 𝒢.big g}, ω g sl p =
            ∑ p : {p : ℕ // p ∈ 𝒢.big g}, (if p = x₀ g sl then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hω, if_neg hsl]
        have h3 : ∑ p : {p : ℕ // p ∈ 𝒢.big g}, (if p = x₀ g sl then (1 : ℝ) else 0) = 1 :=
          (Finset.sum_eq_single_of_mem
            (f := fun p : {p : ℕ // p ∈ 𝒢.big g} => if p = x₀ g sl then (1 : ℝ) else 0)
            (x₀ g sl) (Finset.mem_univ _) (fun p _ hp' => if_neg hp')).trans
              (if_pos rfl)
        exact (h2.trans h3).le
    -- the integral is a product over the slots
    have hsum : ∑ x : LabelList 𝒢.big J ℓ, ∏ g, ∏ sl, ω g sl (x g sl) =
        ∏ g : B, ∏ sl : Slot J ℓ, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, ω g sl p := by
      have h2 : ∑ x : LabelList 𝒢.big J ℓ, ∏ g, ∏ sl, ω g sl (x g sl) =
          ∏ g : B, ∑ w : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}, ∏ sl, ω g sl (w sl) :=
        (Fintype.prod_sum fun (g : B) (w : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) =>
          ∏ sl, ω g sl (w sl)).symm
      rw [h2]
      refine Finset.prod_congr rfl fun g _ => ?_
      exact (Fintype.prod_sum fun (sl : Slot J ℓ) (p : {p : ℕ // p ∈ 𝒢.big g}) =>
        ω g sl p).symm
    have hgroup : ∀ g, ∏ sl : Slot J ℓ,
        (hrW (hrPtMass 𝒢 q n g) (pv g sl) * (if sl ∈ F g then M1 else 1)) =
          (∏ sl, hrW (hrPtMass 𝒢 q n g) (pv g sl)) * M1 ^ (F g).card := by
      intro g
      rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
    calc ∑ x : LabelList 𝒢.big J ℓ,
          (if (∀ g sl, sl ∉ F g → x g sl = x₀ g sl) ∧
              (∀ g sl z, pv g sl = some z → sl ∈ F g ∧ (x g sl : ℕ) = z) then
            ∏ g, ∏ sl ∈ F g, tiltLaw (𝒢.big g) q n (x g sl)
          else 0)
        ≤ ∑ x : LabelList 𝒢.big J ℓ, ∏ g, ∏ sl, ω g sl (x g sl) :=
          Finset.sum_le_sum fun x _ => hterm x
      _ = ∏ g : B, ∏ sl : Slot J ℓ, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, ω g sl p := hsum
      _ ≤ ∏ g : B, ∏ sl : Slot J ℓ,
            (hrW (hrPtMass 𝒢 q n g) (pv g sl) * (if sl ∈ F g then M1 else 1)) :=
          Finset.prod_le_prod
            (fun g _ => Finset.prod_nonneg fun sl _ => Finset.sum_nonneg fun p _ => hω0 g sl p)
            (fun g _ => Finset.prod_le_prod
              (fun sl _ => Finset.sum_nonneg fun p _ => hω0 g sl p) (fun sl _ => hslot g sl))
      _ = (∏ g, ∏ sl, hrW (hrPtMass 𝒢 q n g) (pv g sl)) * ∏ g, M1 ^ (F g).card := by
          rw [Finset.prod_congr rfl fun g _ => hgroup g, Finset.prod_mul_distrib]
  · -- a slot with a prescribed value is outside `F`: every term vanishes
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun x _ => ?_)) hRHS
    exact if_neg fun hc => hsub fun g sl z hz => (hc.2 g sl z hz).1

end HrLists

/-! ### Ordered ghost batches -/

section HrBatches

variable {S B : Type} {𝒢 : GroupFamily S B} {Bc : ℕ} {g : B}

/-- **The prime born at the index `j` of an ordered ghost batch**, if the batch is that large
[S-02:1056–1061] ("a ghost address is performed precisely when its batch is at least that
large"); this is the value of `History.birth` at a ghost address. -/
def hrBatchBirth (β : Batch 𝒢 Bc g) (j : Fin Bc) : Option ℕ :=
  if hj : j.val < β.1.val then some (β.2 ⟨j.val, hj⟩ : ℕ) else none

open _root_.Classical in
/-- **The ordered batch integral with prescribed coordinates** [S-02:1130–1133]: "keep its ordered
batch integral and factorial divisor; constraining indicated fresh coordinates replaces their mass
factors by the same single-point bound". For batches of a given size `b`, the sum of
`∏_j μ̃_g(β_j)` over the batches in which every index with a prescribed value is performed and
carries that value is at most the product of the point masses of the prescribed values times the
sum over all batches of size `b`. Here `μ̃_g(𝒫_g) ≥ 1`. -/
theorem hr_sum_batch_le {q : ℝ} {n : ℕ} (hν : ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p)
    (h1 : 1 ≤ ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) q n p) (b : Fin (Bc + 1))
    (pin : Fin Bc → Option ℕ) :
    ∑ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
        (if ∀ j z, pin j = some z → hrBatchBirth (⟨b, β⟩ : Batch 𝒢 Bc g) j = some z then
          ∏ j, tiltLaw (𝒢.big g) q n (β j) else 0) ≤
      (∏ j, hrW (hrPtMass 𝒢 q n g) (pin j)) *
        ∑ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g}, ∏ j, tiltLaw (𝒢.big g) q n (β j) := by
  have hbB : b.val ≤ Bc := Nat.le_of_lt_succ b.isLt
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) q n p := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := hMdef ▸ h1
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hW0 : ∀ j, 0 ≤ hrW (hrPtMass 𝒢 q n g) (pin j) := fun j =>
    hrW_nonneg (hrPtMass_nonneg hν) _
  -- the total mass of the batches of size `b`
  have htot : ∑ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g}, ∏ j, tiltLaw (𝒢.big g) q n (β j) =
      M ^ b.val := by
    have h3 : ∑ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g}, ∏ j, tiltLaw (𝒢.big g) q n (β j) =
        ∏ _j : Fin b.val, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) q n p :=
      (Fintype.prod_sum fun (_ : Fin b.val) (p : {p : ℕ // p ∈ 𝒢.big g}) =>
        tiltLaw (𝒢.big g) q n p).symm
    rw [h3, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_coe_sort (𝒢.big g) fun p => tiltLaw (𝒢.big g) q n p, hMdef]
  rw [htot]
  have hRHS : 0 ≤ (∏ j, hrW (hrPtMass 𝒢 q n g) (pin j)) * M ^ b.val :=
    mul_nonneg (Finset.prod_nonneg fun j _ => hW0 j) (pow_nonneg hM0 _)
  by_cases hlt : ∀ j z, pin j = some z → j.val < b.val
  · -- the weights of one coordinate
    obtain ⟨ω, hω⟩ : ∃ ω : Fin b.val → {p : ℕ // p ∈ 𝒢.big g} → ℝ, ∀ j p,
        ω j p = if ∀ z, pin (Fin.castLE hbB j) = some z → (p : ℕ) = z then
          tiltLaw (𝒢.big g) q n p else 0 := ⟨_, fun _ _ => rfl⟩
    have hω0 : ∀ j p, 0 ≤ ω j p := by
      intro j p
      rw [hω]
      split_ifs
      · exact hν _ p.2
      · exact le_rfl
    have hterm : ∀ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
        (if ∀ j z, pin j = some z → hrBatchBirth (⟨b, β⟩ : Batch 𝒢 Bc g) j = some z then
          ∏ j, tiltLaw (𝒢.big g) q n (β j) else 0) ≤ ∏ j, ω j (β j) := by
      intro β
      by_cases hc : ∀ j z, pin j = some z → hrBatchBirth (⟨b, β⟩ : Batch 𝒢 Bc g) j = some z
      · rw [if_pos hc]
        refine le_of_eq (Finset.prod_congr rfl fun j _ => ?_)
        rw [hω]
        refine (if_pos fun z hz => ?_).symm
        have h2 := hc (Fin.castLE hbB j) z hz
        have h3 : hrBatchBirth (⟨b, β⟩ : Batch 𝒢 Bc g) (Fin.castLE hbB j) =
            some (β j : ℕ) := dif_pos j.isLt
        rw [h3] at h2
        exact Option.some.inj h2
      · rw [if_neg hc]
        exact Finset.prod_nonneg fun j _ => hω0 j _
    have hslot : ∀ j : Fin b.val, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, ω j p ≤
        hrW (hrPtMass 𝒢 q n g) (pin (Fin.castLE hbB j)) * M := by
      intro j
      exact le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => hω j p))
        (hr_sum_pin_le hν hMdef.ge hM1 (pin (Fin.castLE hbB j)))
    -- the prescribed indices are below `b`
    have hprodW : ∏ j : Fin b.val, hrW (hrPtMass 𝒢 q n g) (pin (Fin.castLE hbB j)) =
        ∏ j : Fin Bc, hrW (hrPtMass 𝒢 q n g) (pin j) := by
      have h2 : ∏ j ∈ Finset.univ.map (Fin.castLEEmb hbB), hrW (hrPtMass 𝒢 q n g) (pin j) =
          ∏ j : Fin Bc, hrW (hrPtMass 𝒢 q n g) (pin j) := by
        refine Finset.prod_subset (Finset.subset_univ _) fun j _ hj => ?_
        have hge : ¬j.val < b.val := fun hjb =>
          hj (Finset.mem_map.mpr ⟨⟨j.val, hjb⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        cases hp : pin j with
        | none => exact hrW_none _
        | some z => exact absurd (hlt j z hp) hge
      rw [← h2, Finset.prod_map]
      rfl
    calc ∑ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
          (if ∀ j z, pin j = some z → hrBatchBirth (⟨b, β⟩ : Batch 𝒢 Bc g) j = some z then
            ∏ j, tiltLaw (𝒢.big g) q n (β j) else 0)
        ≤ ∑ β : Fin b.val → {p : ℕ // p ∈ 𝒢.big g}, ∏ j, ω j (β j) :=
          Finset.sum_le_sum fun β _ => hterm β
      _ = ∏ j : Fin b.val, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, ω j p :=
          (Fintype.prod_sum fun (j : Fin b.val) (p : {p : ℕ // p ∈ 𝒢.big g}) => ω j p).symm
      _ ≤ ∏ j : Fin b.val, (hrW (hrPtMass 𝒢 q n g) (pin (Fin.castLE hbB j)) * M) :=
          Finset.prod_le_prod (fun j _ => Finset.sum_nonneg fun p _ => hω0 j p)
            (fun j _ => hslot j)
      _ = (∏ j, hrW (hrPtMass 𝒢 q n g) (pin j)) * M ^ b.val := by
          rw [Finset.prod_mul_distrib, hprodW, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]
  · -- an index with a prescribed value is not performed: every term vanishes
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun β _ => ?_)) hRHS
    refine if_neg fun hc => hlt fun j z hz => ?_
    by_contra hjb
    have h3 : hrBatchBirth (⟨b, β⟩ : Batch 𝒢 Bc g) j = none := dif_neg hjb
    have h2 := hc j z hz
    rw [h3] at h2
    exact Option.some_ne_none z h2.symm

end HrBatches

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
