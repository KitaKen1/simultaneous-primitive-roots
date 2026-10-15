module

public import SimultaneousPrimitiveRoots.ResearchNoteBounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace SimultaneousPrimitiveRoots

noncomputable section
open Classical

def dyadicBadExponents (B : Set ℕ) (j : ℕ) : Finset ℕ :=
  (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter (fun q => q ∈ B)

theorem badReciprocalWeight_zero (B : Set ℕ) : badReciprocalWeight B 0 = 0 := by
  simp [badReciprocalWeight]

theorem mem_dyadicBadExponents_log {B : Set ℕ} {q : ℕ} (hq : q ≠ 0) (hB : q ∈ B) :
    q ∈ dyadicBadExponents B (Nat.log 2 q) := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
    ⟨Nat.pow_log_le_self 2 hq, Nat.lt_pow_succ_log_self (by omega) q⟩, hB⟩

theorem dyadicBadExponents_weight_le (B : Set ℕ) (j : ℕ) :
    (∑ q ∈ dyadicBadExponents B j, badReciprocalWeight B q) ≤
      ((dyadicBadExponents B j).card : ℝ) / (2 : ℝ) ^ j := by
  calc
    _ ≤ ∑ _q ∈ dyadicBadExponents B j, 1 / (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hqr, hqB⟩ := Finset.mem_filter.mp hq
      have hlow : (2 : ℝ) ^ j ≤ (q : ℝ) := by
        exact_mod_cast (Finset.mem_Ico.mp hqr).1
      rw [badReciprocalWeight, if_pos hqB]
      exact one_div_le_one_div_of_le (by positivity) hlow
    _ = _ := by simp [div_eq_mul_inv]

/-- Any summable envelope for the dyadic reciprocal masses gives KR. This
lemma does not require B to consist of primes. -/
theorem badReciprocalWeight_summable_of_dyadic_envelope (B : Set ℕ) (e : ℕ → ℝ)
    (he : Summable e)
    (hblocks : ∀ j, (∑ q ∈ dyadicBadExponents B j, badReciprocalWeight B q) ≤ e j) :
    Summable (badReciprocalWeight B) := by
  apply summable_of_sum_le (fun q => badReciprocalWeight_nonneg B q)
  intro S
  let J := S.image (Nat.log 2)
  calc
    (∑ q ∈ S, badReciprocalWeight B q) ≤
        ∑ q ∈ S, ∑ j ∈ J,
          if q ∈ dyadicBadExponents B j then badReciprocalWeight B q else 0 := by
      apply Finset.sum_le_sum
      intro q hqS
      by_cases hq : q = 0
      · subst q
        simp [badReciprocalWeight_zero]
      by_cases hqB : q ∈ B
      · have hqblock := mem_dyadicBadExponents_log hq hqB
        have hj : Nat.log 2 q ∈ J := Finset.mem_image.mpr ⟨q, hqS, rfl⟩
        simpa only [if_pos hqblock] using
          Finset.single_le_sum (f := fun j : ℕ =>
            if q ∈ dyadicBadExponents B j then badReciprocalWeight B q else 0) (fun j _ => by
            split_ifs
            · exact badReciprocalWeight_nonneg B q
            · exact le_rfl) hj
      · simp [badReciprocalWeight, hqB]
    _ = ∑ j ∈ J, ∑ q ∈ S,
        if q ∈ dyadicBadExponents B j then badReciprocalWeight B q else 0 :=
      Finset.sum_comm
    _ ≤ ∑ j ∈ J, e j := by
      apply Finset.sum_le_sum
      intro j _
      calc
        (∑ q ∈ S, if q ∈ dyadicBadExponents B j then badReciprocalWeight B q else 0) =
            ∑ q ∈ S.filter (fun q => q ∈ dyadicBadExponents B j), badReciprocalWeight B q := by
          rw [Finset.sum_filter]
        _ ≤ ∑ q ∈ dyadicBadExponents B j, badReciprocalWeight B q := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro q hq
            exact (Finset.mem_filter.mp hq).2
          · intro q _ _
            exact badReciprocalWeight_nonneg B q
        _ ≤ e j := hblocks j
    _ ≤ ∑' j, e j := by
      apply Summable.sum_le_tsum
      · intro j _
        exact (Finset.sum_nonneg fun q _ => badReciprocalWeight_nonneg B q).trans (hblocks j)
      · exact he

/-- Dyadic version of the note's sufficient ZD input. Finite initial blocks can
be absorbed into D. No zero-density theorem is asserted by this definition. -/
def DyadicBadExponentBound (B : Set ℕ) (D ε : ℝ) : Prop :=
  ∀ j : ℕ, ((dyadicBadExponents B j).card : ℝ) ≤
    D * (2 : ℝ) ^ j / ((j : ℝ) + 1) ^ (1 + ε)

theorem badReciprocalWeight_summable_of_dyadic_bound {B : Set ℕ} {D ε : ℝ}
    (hε : 0 < ε) (hZD : DyadicBadExponentBound B D ε) :
    Summable (badReciprocalWeight B) := by
  let e : ℕ → ℝ := fun j => D / ((j : ℝ) + 1) ^ (1 + ε)
  have he : Summable e := by
    have hp := (Real.summable_one_div_nat_add_rpow (1 : ℝ) (1 + ε)).2 (by linarith)
    have habs : ∀ j : ℕ, |(j : ℝ) + 1| = (j : ℝ) + 1 := fun j => abs_of_nonneg (by positivity)
    simpa [e, div_eq_mul_inv, habs] using hp.mul_left D
  apply badReciprocalWeight_summable_of_dyadic_envelope B e he
  intro j
  calc
    _ ≤ ((dyadicBadExponents B j).card : ℝ) / (2 : ℝ) ^ j :=
      dyadicBadExponents_weight_le B j
    _ ≤ (D * (2 : ℝ) ^ j / ((j : ℝ) + 1) ^ (1 + ε)) / (2 : ℝ) ^ j :=
      div_le_div_of_nonneg_right (hZD j) (by positivity)
    _ = e j := by
      dsimp [e]
      field_simp

/-- A density estimate need only hold after finitely many blocks. The initial
blocks are finite and are handled by summability, without an explicit constant. -/
theorem badReciprocalWeight_summable_of_eventual_dyadic_bound {B : Set ℕ} {D ε : ℝ}
    (hε : 0 < ε)
    (hZD : ∀ᶠ j : ℕ in Filter.atTop, ((dyadicBadExponents B j).card : ℝ) ≤
      D * (2 : ℝ) ^ j / ((j : ℝ) + 1) ^ (1 + ε)) :
    Summable (badReciprocalWeight B) := by
  let e : ℕ → ℝ := fun j => D / ((j : ℝ) + 1) ^ (1 + ε)
  have he : Summable e := by
    have hp := (Real.summable_one_div_nat_add_rpow (1 : ℝ) (1 + ε)).2 (by linarith)
    have habs : ∀ j : ℕ, |(j : ℝ) + 1| = (j : ℝ) + 1 := fun j => abs_of_nonneg (by positivity)
    simpa [e, div_eq_mul_inv, habs] using hp.mul_left D
  let mass : ℕ → ℝ := fun j => ∑ q ∈ dyadicBadExponents B j, badReciprocalWeight B q
  have hm : Summable mass := by
    apply he.of_norm_bounded_eventually
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hZD] with j hj
    rw [Real.norm_eq_abs, abs_of_nonneg
      (Finset.sum_nonneg fun q _ => badReciprocalWeight_nonneg B q)]
    calc
      _ ≤ ((dyadicBadExponents B j).card : ℝ) / (2 : ℝ) ^ j :=
        dyadicBadExponents_weight_le B j
      _ ≤ (D * (2 : ℝ) ^ j / ((j : ℝ) + 1) ^ (1 + ε)) / (2 : ℝ) ^ j :=
        div_le_div_of_nonneg_right hj (by positivity)
      _ = e j := by dsimp [e]; field_simp
  exact badReciprocalWeight_summable_of_dyadic_envelope B mass hm fun _ => le_rfl

open Filter Topology in
theorem researchNote_cutoff_tendsto :
    Tendsto (fun x : ℝ => Nat.floor ((Real.log x) ^ (1 / 4 : ℝ))) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp Real.tendsto_log_atTop)

/-- Connect the actual floored logarithmic cutoff with the finite zero height.
The floor weakens no strict inequality: floor(t)<q implies t<q. -/
theorem researchNote_large_cutoff_height {x δ : ℝ} {q : ℕ} (hx : 1 ≤ x)
    (hδ : δ < 1 / 2) (hq : Nat.floor ((Real.log x) ^ (1 / 4 : ℝ)) < q) :
    Real.sqrt (8 * δ * Real.log x) < 2 * (q : ℝ) ^ 2 := by
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hroot : (Real.log x) ^ (1 / 4 : ℝ) < (q : ℝ) := Nat.lt_of_floor_lt hq
  have hpow : Real.log x = ((Real.log x) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
    norm_num
  have hlarge : Real.log x < (q : ℝ) ^ (4 : ℕ) := by
    rw [hpow]
    gcongr
  exact researchNote_height_below_quadratic hL hδ hqpos hlarge

open Filter in
theorem mainClaim_of_dyadic_sparse_bounds {η : ℝ} (hηhalf : η < 1 / 2)
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A η θ)
    (hsparse : ∀ A : Finset ℕ, Admissible A →
      ∃ K C D ε : ℝ, ∃ B : Set ℕ, ∃ Q : ℝ → ℕ,
        0 ≤ K ∧ 0 ≤ C ∧ 0 < ε ∧ DyadicBadExponentBound B D ε ∧
        Tendsto Q atTop atTop ∧ SparseGoodPowerResidueBound A η K B Q ∧
        SparseBadPowerResidueBound A η C B Q) : MainClaim := by
  apply mainClaim_of_sparse_bounds hηhalf hsupply
  intro A hA
  obtain ⟨K, C, D, ε, B, Q, hK, hC, hε, hZD, hQ, hg, hb⟩ := hsparse A hA
  exact ⟨K, C, B, Q, hK, hC,
    badReciprocalWeight_summable_of_dyadic_bound hε hZD, hQ, hg, hb⟩

end

end SimultaneousPrimitiveRoots
