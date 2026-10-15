module

public import SimultaneousPrimitiveRoots.CandidateSets
public import SimultaneousPrimitiveRoots.MovingCutoff

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Filter

/-- The exact uniform counting input still to be proved by the analytic route.
The moving q range is inside the eventual quantifier. -/
def UniformPowerResidueBound (A : Finset ℕ) (δ η C : ℝ) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ a ∈ A, ∀ q : ℕ, q.Prime → a < q → q ≤ ⌊2 * x ^ η⌋₊ →
    ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
      C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
        C * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) / Real.log x

theorem powerResidueExceptionUnion_card_le_sum (A : Finset ℕ) (Y : ℕ) (η x : ℝ) :
    ((powerResidueExceptionUnion A Y η x).card : ℝ) ≤
      ∑ a ∈ A, ∑ q ∈ mediumObstructionPrimes Y η x,
        ((powerResidueExceptionPrimes a q x).card : ℝ) := by
  classical
  calc
    ((powerResidueExceptionUnion A Y η x).card : ℝ) ≤
        ∑ a ∈ A, (((mediumObstructionPrimes Y η x).biUnion fun q =>
          powerResidueExceptionPrimes a q x).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := A)
        (t := fun a => (mediumObstructionPrimes Y η x).biUnion fun q =>
          powerResidueExceptionPrimes a q x))
    _ ≤ ∑ a ∈ A, ∑ q ∈ mediumObstructionPrimes Y η x,
        ((powerResidueExceptionPrimes a q x).card : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      exact_mod_cast (Finset.card_biUnion_le (s := mediumObstructionPrimes Y η x)
        (t := fun q => powerResidueExceptionPrimes a q x))

/-- Only integer tail sums and a crude logarithmic bound are used in this aggregation. -/
theorem powerResidueExceptionUnion_card_bound {A : Finset ℕ} {Y : ℕ}
    {δ η C x : ℝ} (hY : 1 ≤ Y) (hC : 0 ≤ C) (hη : 0 ≤ η) (hx : 2 ≤ x)
    (hcount : ∀ a ∈ A, ∀ q ∈ mediumObstructionPrimes Y η x,
      ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
        C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
          C * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) / Real.log x) :
    ((powerResidueExceptionUnion A Y η x).card : ℝ) ≤
      ((A.card : ℝ) * C / (Y : ℝ)) * (x / Real.log x) +
        splittingErrorEnvelope ((A.card : ℝ) * C) δ η x := by
  classical
  let S := mediumObstructionPrimes Y η x
  have hS : ∀ q ∈ S, q.Prime ∧ Y < q ∧ q ≤ ⌊2 * x ^ η⌋₊ := by
    intro q hq
    obtain ⟨hqr, hprime, hqY⟩ := Finset.mem_filter.mp hq
    exact ⟨hprime, hqY, Nat.lt_succ_iff.mp (Finset.mem_range.mp hqr)⟩
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hscale : 0 ≤ C * (x / Real.log x) := by positivity
  have herror : 0 ≤ C * x ^ (1 - δ) / Real.log x := by positivity
  have htail := reciprocal_tail_finset_le hY S (fun q hq => (hS q hq).2.1)
  have hlogs := sum_log_twice_le (moving_cutoff_pos hη hx)
    (fun q hq => ⟨(hS q hq).1.one_lt.le, (hS q hq).2.2⟩)
  have hsum : (∑ q ∈ S,
      (C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
        C * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) / Real.log x)) ≤
      (C / (Y : ℝ)) * (x / Real.log x) + splittingErrorEnvelope C δ η x := by
    calc
      (∑ q ∈ S,
          (C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
            C * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) / Real.log x)) =
          (C * (x / Real.log x)) * (∑ q ∈ S, 1 / ((q : ℝ) * ((q : ℝ) - 1))) +
            (C * x ^ (1 - δ) / Real.log x) * (∑ q ∈ S, Real.log (2 * (q : ℝ))) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ ≤ (C * (x / Real.log x)) * (1 / (Y : ℝ)) +
          (C * x ^ (1 - δ) / Real.log x) *
            (((⌊2 * x ^ η⌋₊ : ℝ) + 1) * Real.log (2 * (⌊2 * x ^ η⌋₊ : ℝ))) :=
        add_le_add (mul_le_mul_of_nonneg_left htail hscale)
          (mul_le_mul_of_nonneg_left hlogs herror)
      _ = (C / (Y : ℝ)) * (x / Real.log x) + splittingErrorEnvelope C δ η x := by
        unfold splittingErrorEnvelope
        ring
  calc
    ((powerResidueExceptionUnion A Y η x).card : ℝ) ≤
        ∑ a ∈ A, ∑ q ∈ S, ((powerResidueExceptionPrimes a q x).card : ℝ) :=
      powerResidueExceptionUnion_card_le_sum A Y η x
    _ ≤ ∑ _a ∈ A, ((C / (Y : ℝ)) * (x / Real.log x) + splittingErrorEnvelope C δ η x) := by
      apply Finset.sum_le_sum
      intro a ha
      exact (Finset.sum_le_sum (fun q hq => hcount a ha q hq)).trans hsum
    _ = ((A.card : ℝ) * C / (Y : ℝ)) * (x / Real.log x) +
        splittingErrorEnvelope ((A.card : ℝ) * C) δ η x := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      unfold splittingErrorEnvelope
      ring

theorem powerResidueExceptionUnion_eventually_bound {A : Finset ℕ} {Y : ℕ}
    {δ η C : ℝ} (hY : 1 ≤ Y) (hYbase : ∀ a ∈ A, a ≤ Y) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hcount : UniformPowerResidueBound A δ η C) :
    ∀ᶠ x : ℝ in atTop, ((powerResidueExceptionUnion A Y η x).card : ℝ) ≤
      ((A.card : ℝ) * C / (Y : ℝ)) * (x / Real.log x) +
        splittingErrorEnvelope ((A.card : ℝ) * C) δ η x := by
  filter_upwards [hcount, eventually_ge_atTop (2 : ℝ)] with x hxcount hx
  apply powerResidueExceptionUnion_card_bound hY hC hη hx
  intro a ha q hq
  obtain ⟨hqr, hprime, hqY⟩ := Finset.mem_filter.mp hq
  exact hxcount a ha q hprime ((hYbase a ha).trans_lt hqY)
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hqr))

end SimultaneousPrimitiveRoots
