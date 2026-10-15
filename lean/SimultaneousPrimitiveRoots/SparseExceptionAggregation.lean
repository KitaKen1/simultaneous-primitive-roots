module

public import SimultaneousPrimitiveRoots.FixedBaseRemainder

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Filter Topology Asymptotics

noncomputable section

open Classical

/-- Abstract reciprocal weight of a fixed exceptional set. Identifying B with
the Hecke-zero exceptional set of research_note_ja.md is separate analytic work. -/
def badReciprocalWeight (B : Set ℕ) (q : ℕ) : ℝ :=
  if q ∈ B then 1 / (q : ℝ) else 0

def badReciprocalTail (B : Set ℕ) (n : ℕ) : ℝ :=
  ∑' q, if n < q then badReciprocalWeight B q else 0

theorem badReciprocalWeight_nonneg (B : Set ℕ) (q : ℕ) :
    0 ≤ badReciprocalWeight B q := by
  unfold badReciprocalWeight
  split <;> positivity

theorem badReciprocalTail_summable (B : Set ℕ) (n : ℕ)
    (hB : Summable (badReciprocalWeight B)) :
    Summable (fun q => if n < q then badReciprocalWeight B q else 0) := by
  apply hB.of_norm_bounded
  intro q
  split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg, badReciprocalWeight_nonneg]

theorem badReciprocalTail_nonneg (B : Set ℕ) (n : ℕ) :
    0 ≤ badReciprocalTail B n := by
  apply tsum_nonneg
  intro q
  split_ifs
  · exact badReciprocalWeight_nonneg B q
  · exact le_rfl

theorem sum_bad_reciprocals_le_tail (B : Set ℕ) (n : ℕ) (S : Finset ℕ)
    (hB : Summable (badReciprocalWeight B)) :
    (∑ q ∈ S.filter (fun q => n < q ∧ q ∈ B), 1 / (q : ℝ)) ≤
      badReciprocalTail B n := by
  calc
    _ = ∑ q ∈ S.filter (fun q => n < q ∧ q ∈ B),
        (if n < q then badReciprocalWeight B q else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      obtain ⟨_, hn, hqB⟩ := Finset.mem_filter.mp hq
      simp [hn, hqB, badReciprocalWeight]
    _ ≤ badReciprocalTail B n := by
      apply Summable.sum_le_tsum
      · intro q _
        split_ifs
        · exact badReciprocalWeight_nonneg B q
        · exact le_rfl
      · exact badReciprocalTail_summable B n hB

/-- Summability, rather than finiteness of B, suffices. -/
theorem badReciprocalTail_tendsto (B : Set ℕ)
    (hB : Summable (badReciprocalWeight B)) :
    Tendsto (badReciprocalTail B) atTop (𝓝 0) := by
  have hterm : ∀ q : ℕ, Tendsto
      (fun n : ℕ => if n < q then badReciprocalWeight B q else 0) atTop (𝓝 (0 : ℝ)) := by
    intro q
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop q] with n hn
    simp [not_lt.mpr hn]
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ q,
      ‖if n < q then badReciprocalWeight B q else 0‖ ≤ badReciprocalWeight B q := by
    apply Eventually.of_forall
    intro n q
    split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg, badReciprocalWeight_nonneg]
  change Tendsto (fun n : ℕ => ∑' q,
    if n < q then badReciprocalWeight B q else 0) atTop (𝓝 0)
  simpa only [tsum_zero] using
    tendsto_tsum_of_dominated_convergence hB hterm hbound

theorem badReciprocalTail_isLittleO (B : Set ℕ) (Q : ℝ → ℕ) (D : ℝ)
    (hB : Summable (badReciprocalWeight B)) (hQ : Tendsto Q atTop atTop) :
    (fun x => D * (x / Real.log x) * badReciprocalTail B (Q x))
      =o[atTop] (fun x => x / Real.log x) := by
  have htail : (fun x => badReciprocalTail B (Q x))
      =o[atTop] (fun _ : ℝ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 ((badReciprocalTail_tendsto B hB).comp hQ)
  have hprod := htail.mul_isBigO (isBigO_refl (fun x : ℝ => x / Real.log x) atTop)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hprod.const_mul_left D

def sparseGoodExceptionSum (A : Finset ℕ) (Y : ℕ) (η : ℝ)
    (B : Set ℕ) (Q : ℝ → ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ A, ∑ q ∈ (mediumObstructionPrimes Y η x).filter
    (fun q => ¬ (Q x < q ∧ q ∈ B)), ((powerResidueExceptionPrimes a q x).card : ℝ)

def sparseBadExceptionSum (A : Finset ℕ) (Y : ℕ) (η : ℝ)
    (B : Set ℕ) (Q : ℝ → ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ A, ∑ q ∈ (mediumObstructionPrimes Y η x).filter
    (fun q => Q x < q ∧ q ∈ B), ((powerResidueExceptionPrimes a q x).card : ℝ)

theorem sparseExceptionSum_partition (A : Finset ℕ) (Y : ℕ) (η : ℝ)
    (B : Set ℕ) (Q : ℝ → ℕ) (x : ℝ) :
    (∑ a ∈ A, ∑ q ∈ mediumObstructionPrimes Y η x,
      ((powerResidueExceptionPrimes a q x).card : ℝ)) =
        sparseGoodExceptionSum A Y η B Q x + sparseBadExceptionSum A Y η B Q x := by
  unfold sparseGoodExceptionSum sparseBadExceptionSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  symm
  simpa only [add_comm] using Finset.sum_filter_add_sum_filter_not
    (mediumObstructionPrimes Y η x) (fun q => Q x < q ∧ q ∈ B)
    (fun q => ((powerResidueExceptionPrimes a q x).card : ℝ))

/-- Small q, including bad ones, and large good q. K must be independent of Y.
The analytic estimates for these terms are not supplied by this definition. -/
def SparseGoodPowerResidueBound (A : Finset ℕ) (η K : ℝ)
    (B : Set ℕ) (Q : ℝ → ℕ) : Prop :=
  ∀ Y : ℕ, 1 ≤ Y → (∀ a ∈ A, a ≤ Y) →
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x => x / Real.log x) ∧
      ∀ᶠ x : ℝ in atTop, sparseGoodExceptionSum A Y η B Q x ≤
        (K / (Y : ℝ)) * (x / Real.log x) + E x

/-- A Brun--Titchmarsh type bound on the actual exceptions in the bad set.
This remains an unproved analytic input; a count of all primes does not suffice. -/
def SparseBadPowerResidueBound (A : Finset ℕ) (η C : ℝ)
    (B : Set ℕ) (Q : ℝ → ℕ) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ a ∈ A, ∀ q : ℕ, q.Prime → Q x < q → q ∈ B →
    q ≤ Nat.floor (2 * x ^ η) → ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
      C * (x / Real.log x) * (1 / (q : ℝ))

theorem sparseBadExceptionSum_le_tail {A : Finset ℕ} {Y : ℕ} {η C : ℝ}
    {B : Set ℕ} {Q : ℝ → ℕ} {x : ℝ} (hC : 0 ≤ C) (hx : 2 ≤ x)
    (hB : Summable (badReciprocalWeight B))
    (hcount : ∀ a ∈ A, ∀ q ∈ mediumObstructionPrimes Y η x, Q x < q → q ∈ B →
      ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
        C * (x / Real.log x) * (1 / (q : ℝ))) :
    sparseBadExceptionSum A Y η B Q x ≤
      (A.card : ℝ) * C * (x / Real.log x) * badReciprocalTail B (Q x) := by
  have hscale : 0 ≤ C * (x / Real.log x) := by
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    positivity
  unfold sparseBadExceptionSum
  calc
    _ ≤ ∑ _a ∈ A, C * (x / Real.log x) * badReciprocalTail B (Q x) := by
      apply Finset.sum_le_sum
      intro a ha
      calc
        _ ≤ ∑ q ∈ (mediumObstructionPrimes Y η x).filter
            (fun q => Q x < q ∧ q ∈ B), C * (x / Real.log x) * (1 / (q : ℝ)) := by
          apply Finset.sum_le_sum
          intro q hq
          obtain ⟨hqS, hn, hqB⟩ := Finset.mem_filter.mp hq
          exact hcount a ha q hqS hn hqB
        _ = C * (x / Real.log x) * (∑ q ∈ (mediumObstructionPrimes Y η x).filter
            (fun q => Q x < q ∧ q ∈ B), 1 / (q : ℝ)) := by rw [Finset.mul_sum]
        _ ≤ C * (x / Real.log x) * badReciprocalTail B (Q x) :=
          mul_le_mul_of_nonneg_left
            (sum_bad_reciprocals_le_tail B (Q x) (mediumObstructionPrimes Y η x) hB) hscale
    _ = _ := by simp [mul_assoc]

theorem summedPowerResidueBound_of_sparse {A : Finset ℕ} {η K C : ℝ}
    {B : Set ℕ} {Q : ℝ → ℕ} (hC : 0 ≤ C)
    (hB : Summable (badReciprocalWeight B)) (hQ : Tendsto Q atTop atTop)
    (hgood : SparseGoodPowerResidueBound A η K B Q)
    (hbad : SparseBadPowerResidueBound A η C B Q) :
    SummedPowerResidueBound A η K := by
  intro Y hY hbase
  obtain ⟨E, hE, hg⟩ := hgood Y hY hbase
  let R : ℝ → ℝ := fun x => (A.card : ℝ) * C * (x / Real.log x) * badReciprocalTail B (Q x)
  have hR : R =o[atTop] (fun x => x / Real.log x) :=
    badReciprocalTail_isLittleO B Q ((A.card : ℝ) * C) hB hQ
  refine ⟨fun x => E x + R x, hE.add hR, ?_⟩
  filter_upwards [hg, hbad, eventually_ge_atTop (2 : ℝ)] with x hxg hxb hx
  rw [sparseExceptionSum_partition A Y η B Q x]
  have hb := sparseBadExceptionSum_le_tail (Y := Y) hC hx hB (fun a ha q hq hn hqB => by
    obtain ⟨hqr, hprime, _⟩ := Finset.mem_filter.mp hq
    have hcut : q ≤ Nat.floor (2 * x ^ η) :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hqr)
    exact hxb a ha q hprime hn hqB hcut)
  have := add_le_add hxg hb
  simpa only [R, add_assoc] using this

/-- Only the finite sums and summable exceptional tail have been proved here.
The actual Hecke exceptional set and both counting inputs still require proofs. -/
theorem mainClaim_of_sparse_bounds {η : ℝ} (hηhalf : η < 1 / 2)
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A η θ)
    (hsparse : ∀ A : Finset ℕ, Admissible A →
      ∃ K C : ℝ, ∃ B : Set ℕ, ∃ Q : ℝ → ℕ,
        0 ≤ K ∧ 0 ≤ C ∧ Summable (badReciprocalWeight B) ∧ Tendsto Q atTop atTop ∧
        SparseGoodPowerResidueBound A η K B Q ∧ SparseBadPowerResidueBound A η C B Q) :
    MainClaim := by
  apply mainClaim_of_summed_bounds hηhalf hsupply
  intro A hA
  obtain ⟨K, C, B, Q, hK, hC, hB, hQ, hg, hb⟩ := hsparse A hA
  exact ⟨K, hK, summedPowerResidueBound_of_sparse hC hB hQ hg hb⟩

end

end SimultaneousPrimitiveRoots
