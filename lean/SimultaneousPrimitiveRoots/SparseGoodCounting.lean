module

public import SimultaneousPrimitiveRoots.SparseExceptionAggregation

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Filter Asymptotics

noncomputable section
open Classical

def sparseSmallExceptionSum (A : Finset ℕ) (Y : ℕ) (η : ℝ)
    (Q : ℝ → ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ A, ∑ q ∈ (mediumObstructionPrimes Y η x).filter (fun q => q ≤ Q x),
    ((powerResidueExceptionPrimes a q x).card : ℝ)

def sparseLargeGoodExceptionSum (A : Finset ℕ) (Y : ℕ) (η : ℝ)
    (B : Set ℕ) (Q : ℝ → ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ A, ∑ q ∈ (mediumObstructionPrimes Y η x).filter
    (fun q => Q x < q ∧ q ∉ B), ((powerResidueExceptionPrimes a q x).card : ℝ)

theorem sparseGoodExceptionSum_partition (A : Finset ℕ) (Y : ℕ) (η : ℝ)
    (B : Set ℕ) (Q : ℝ → ℕ) (x : ℝ) :
    sparseGoodExceptionSum A Y η B Q x = sparseSmallExceptionSum A Y η Q x +
      sparseLargeGoodExceptionSum A Y η B Q x := by
  unfold sparseGoodExceptionSum sparseSmallExceptionSum sparseLargeGoodExceptionSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : Q x < q <;> by_cases hB : q ∈ B <;>
    simp [hq, hB, show q ≤ Q x ↔ ¬ Q x < q from not_lt.symm]

/-- A finite-subsum version of the existing uniform tail aggregation. Primality
is not needed here: the integer reciprocal telescope and a crude log sum suffice. -/
theorem powerResidueExceptionPrimes_sum_bound {Y : ℕ} {S : Finset ℕ}
    {a : ℕ} {δ η C x : ℝ} (hY : 1 ≤ Y) (hC : 0 ≤ C) (hη : 0 ≤ η) (hx : 2 ≤ x)
    (hS : ∀ q ∈ S, Y < q ∧ q ≤ Nat.floor (2 * x ^ η))
    (hcount : ∀ q ∈ S, ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
      C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
        C * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) / Real.log x) :
    (∑ q ∈ S, ((powerResidueExceptionPrimes a q x).card : ℝ)) ≤
      (C / (Y : ℝ)) * (x / Real.log x) + splittingErrorEnvelope C δ η x := by
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hscale : 0 ≤ C * (x / Real.log x) := by positivity
  have herror : 0 ≤ C * x ^ (1 - δ) / Real.log x := by positivity
  have htail := reciprocal_tail_finset_le hY S (fun q hq => (hS q hq).1)
  have hlogs := sum_log_twice_le (moving_cutoff_pos hη hx)
    (fun q hq => ⟨by have := (hS q hq).1; omega, (hS q hq).2⟩)
  calc
    _ ≤ ∑ q ∈ S, (
        C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
          C * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) / Real.log x) :=
      Finset.sum_le_sum hcount
    _ = (C * (x / Real.log x)) * (∑ q ∈ S, 1 / ((q : ℝ) * ((q : ℝ) - 1))) +
        (C * x ^ (1 - δ) / Real.log x) * (∑ q ∈ S, Real.log (2 * (q : ℝ))) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ (C * (x / Real.log x)) * (1 / (Y : ℝ)) +
        (C * x ^ (1 - δ) / Real.log x) *
          (((Nat.floor (2 * x ^ η) : ℝ) + 1) * Real.log (2 * (Nat.floor (2 * x ^ η) : ℝ))) :=
      add_le_add (mul_le_mul_of_nonneg_left htail hscale)
        (mul_le_mul_of_nonneg_left hlogs herror)
    _ = _ := by unfold splittingErrorEnvelope; ring

/-- The small-q analytic input, with the onset and error allowed to depend on Y.
This definition does not prove the classical Dedekind zero estimates. -/
def SmallExponentPowerResidueBound (A : Finset ℕ) (η K : ℝ) (Q : ℝ → ℕ) : Prop :=
  ∀ Y : ℕ, 1 ≤ Y → (∀ a ∈ A, a ≤ Y) →
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x => x / Real.log x) ∧
      ∀ᶠ x : ℝ in atTop, sparseSmallExceptionSum A Y η Q x ≤
        (K / (Y : ℝ)) * (x / Real.log x) + E x

/-- Only large q outside the fixed bad set need the old U-type estimate.
The moving range of q remains inside the eventual quantifier. -/
def LargeGoodPowerResidueBound (A : Finset ℕ) (δ η C : ℝ)
    (B : Set ℕ) (Q : ℝ → ℕ) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ a ∈ A, ∀ q : ℕ, q.Prime → a < q → Q x < q → q ∉ B →
    q ≤ Nat.floor (2 * x ^ η) → ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
      C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
        C * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) / Real.log x

theorem largeGoodPowerResidueBound_of_uniform {A : Finset ℕ} {δ η C : ℝ}
    (h : UniformPowerResidueBound A δ η C) (B : Set ℕ) (Q : ℝ → ℕ) :
    LargeGoodPowerResidueBound A δ η C B Q := by
  filter_upwards [h] with x hx
  intro a ha q hp haq _ _ hcut
  exact hx a ha q hp haq hcut

theorem sparseLargeGoodExceptionSum_eventually_bound {A : Finset ℕ} {Y : ℕ}
    {δ η C : ℝ} {B : Set ℕ} {Q : ℝ → ℕ} (hY : 1 ≤ Y) (hbase : ∀ a ∈ A, a ≤ Y)
    (hC : 0 ≤ C) (hη : 0 ≤ η) (hcount : LargeGoodPowerResidueBound A δ η C B Q) :
    ∀ᶠ x : ℝ in atTop, sparseLargeGoodExceptionSum A Y η B Q x ≤
      ((A.card : ℝ) * C / (Y : ℝ)) * (x / Real.log x) +
        splittingErrorEnvelope ((A.card : ℝ) * C) δ η x := by
  filter_upwards [hcount, eventually_ge_atTop (2 : ℝ)] with x hc hx
  let S := (mediumObstructionPrimes Y η x).filter (fun q => Q x < q ∧ q ∉ B)
  have hS : ∀ q ∈ S, q.Prime ∧ Y < q ∧ Q x < q ∧ q ∉ B ∧ q ≤ Nat.floor (2 * x ^ η) := by
    intro q hq
    obtain ⟨hqM, hlarge, hnot⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqr, hp, hqY⟩ := Finset.mem_filter.mp hqM
    exact ⟨hp, hqY, hlarge, hnot, Nat.lt_succ_iff.mp (Finset.mem_range.mp hqr)⟩
  calc
    sparseLargeGoodExceptionSum A Y η B Q x ≤
        ∑ _a ∈ A, ((C / (Y : ℝ)) * (x / Real.log x) + splittingErrorEnvelope C δ η x) := by
      unfold sparseLargeGoodExceptionSum
      apply Finset.sum_le_sum
      intro a ha
      apply powerResidueExceptionPrimes_sum_bound hY hC hη hx
        (fun q hq => ⟨(hS q hq).2.1, (hS q hq).2.2.2.2⟩)
      intro q hq
      obtain ⟨hp, hqY, hlarge, hnot, hcut⟩ := hS q hq
      exact hc a ha q hp ((hbase a ha).trans_lt hqY) hlarge hnot hcut
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      unfold splittingErrorEnvelope
      ring

theorem sparseGoodPowerResidueBound_of_small_and_large {A : Finset ℕ} {δ η K C : ℝ}
    {B : Set ℕ} {Q : ℝ → ℕ} (hC : 0 ≤ C) (hη : 0 ≤ η) (hηδ : η < δ)
    (hsmall : SmallExponentPowerResidueBound A η K Q)
    (hlarge : LargeGoodPowerResidueBound A δ η C B Q) :
    SparseGoodPowerResidueBound A η (K + (A.card : ℝ) * C) B Q := by
  intro Y hY hbase
  obtain ⟨E, hE, hs⟩ := hsmall Y hY hbase
  have herr := splittingErrorEnvelope_isLittleO (mul_nonneg (Nat.cast_nonneg A.card) hC) hη hηδ
  refine ⟨fun x => E x + splittingErrorEnvelope ((A.card : ℝ) * C) δ η x, hE.add herr, ?_⟩
  filter_upwards [hs, sparseLargeGoodExceptionSum_eventually_bound hY hbase hC hη hlarge]
    with x hxs hxl
  rw [sparseGoodExceptionSum_partition]
  have hsum := add_le_add hxs hxl
  have heq : (K / (Y : ℝ)) * (x / Real.log x) + E x +
      (((A.card : ℝ) * C / (Y : ℝ)) * (x / Real.log x) +
        splittingErrorEnvelope ((A.card : ℝ) * C) δ η x) =
      ((K + (A.card : ℝ) * C) / (Y : ℝ)) * (x / Real.log x) +
        (E x + splittingErrorEnvelope ((A.card : ℝ) * C) δ η x) := by ring
  exact heq ▸ hsum

theorem mainClaim_of_small_large_sparse_bounds {δ η : ℝ} (hη : 0 ≤ η)
    (hηδ : η < δ) (hηhalf : η < 1 / 2)
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A η θ)
    (hsparse : ∀ A : Finset ℕ, Admissible A →
      ∃ K C Cbad : ℝ, ∃ B : Set ℕ, ∃ Q : ℝ → ℕ,
        0 ≤ K ∧ 0 ≤ C ∧ 0 ≤ Cbad ∧ Summable (badReciprocalWeight B) ∧ Tendsto Q atTop atTop ∧
        SmallExponentPowerResidueBound A η K Q ∧ LargeGoodPowerResidueBound A δ η C B Q ∧
        SparseBadPowerResidueBound A η Cbad B Q) : MainClaim := by
  apply mainClaim_of_sparse_bounds hηhalf hsupply
  intro A hA
  obtain ⟨K, C, Cbad, B, Q, hK, hC, hCb, hB, hQ, hs, hl, hb⟩ := hsparse A hA
  exact ⟨K + (A.card : ℝ) * C, Cbad, B, Q,
    add_nonneg hK (mul_nonneg (Nat.cast_nonneg _) hC), hCb, hB, hQ,
    sparseGoodPowerResidueBound_of_small_and_large hC hη hηδ hs hl, hb⟩

end

end SimultaneousPrimitiveRoots
