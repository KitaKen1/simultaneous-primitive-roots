module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Statements

/-!
# The two hypotheses of Proposition 6.3 for the active groups

`Transference.IdealFamilyBound` (the conclusion of [P] Proposition 6.3 / [S] Theorem 4.1) is
stated for prime groups whose big groups are intervals of primes and for a balanced split of the
big groups into two blocks. For the active groups of [P] §6 both are bookkeeping:

* `bigIntervals : BigIntervals`: "Every big group is the set of all primes in an interval"
  (`[P-06:0023]`, the field `ActiveGroups.Admissible.big_interval`) in the form
  `Transference.IsPrimeInterval`: a finite set of primes closed under the primes between two of its
  members is the set of primes of `[min, max]`; the empty set is the set of primes of `[1, 0]`.
* `halfSplit_balanced : HalfSplitBalanced`: the blocks `{i : 2i < n}` and `{i : 2i ≥ n}` of
  `Fin n` have `⌈n/2⌉` and `⌊n/2⌋` elements.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference

/-- **Every big active group is the set of all primes of an interval.** -/
theorem bigIntervals : BigIntervals := by
  intro P x 𝔊 h j
  rcases (𝔊.group (Sum.inr j)).eq_empty_or_nonempty with he | hne
  · refine ⟨1, 0, fun p => ?_⟩
    rw [he]
    constructor
    · intro hp
      exact absurd hp (Finset.notMem_empty p)
    · rintro ⟨_, h1, h2⟩
      exfalso
      omega
  · refine ⟨(𝔊.group (Sum.inr j)).min' hne, (𝔊.group (Sum.inr j)).max' hne, fun p => ?_⟩
    constructor
    · intro hp
      exact ⟨h.prime (Sum.inr j) p hp, Finset.min'_le _ p hp, Finset.le_max' _ p hp⟩
    · rintro ⟨hp, h1, h2⟩
      exact h.big_interval j _ (Finset.min'_mem _ hne) _ (Finset.max'_mem _ hne) p hp h1 h2

/-- **The two blocks of `halfSplit` differ in size by at most one.** -/
theorem halfSplit_balanced : HalfSplitBalanced := by
  intro n
  have hT : (Finset.univ.filter fun g : Fin n => halfSplit n g = true).card ≤ (n + 1) / 2 := by
    have h : (Finset.univ.filter fun g : Fin n => halfSplit n g = true).card ≤
        (Finset.range ((n + 1) / 2)).card := by
      refine Finset.card_le_card_of_injOn (fun i : Fin n => i.val) ?_ ?_
      · intro i hi
        rw [Finset.mem_coe] at hi ⊢
        rw [Finset.mem_filter] at hi
        have h2 : 2 * (i : ℕ) < n := of_decide_eq_true hi.2
        show (i : ℕ) ∈ Finset.range ((n + 1) / 2)
        rw [Finset.mem_range]
        omega
      · intro i _ j _ hij
        exact Fin.ext hij
    rwa [Finset.card_range] at h
  have hF : (Finset.univ.filter fun g : Fin n => halfSplit n g = false).card ≤ n / 2 := by
    have h : (Finset.univ.filter fun g : Fin n => halfSplit n g = false).card ≤
        (Finset.range (n / 2)).card := by
      refine Finset.card_le_card_of_injOn (fun i : Fin n => n - 1 - i.val) ?_ ?_
      · intro i hi
        rw [Finset.mem_coe] at hi ⊢
        rw [Finset.mem_filter] at hi
        have h2 : ¬ 2 * (i : ℕ) < n := of_decide_eq_false hi.2
        have h3 : (i : ℕ) < n := i.isLt
        show n - 1 - (i : ℕ) ∈ Finset.range (n / 2)
        rw [Finset.mem_range]
        omega
      · intro i _ j _ hij
        have hij' : n - 1 - (i : ℕ) = n - 1 - (j : ℕ) := hij
        have h3 : (i : ℕ) < n := i.isLt
        have h4 : (j : ℕ) < n := j.isLt
        exact Fin.ext (by omega)
    rwa [Finset.card_range] at h
  have hsum : (Finset.univ.filter fun g : Fin n => halfSplit n g = true).card +
      (Finset.univ.filter fun g : Fin n => halfSplit n g = false).card = n := by
    have hF' : (Finset.univ.filter fun g : Fin n => halfSplit n g = false) =
        Finset.univ.filter fun g : Fin n => ¬ halfSplit n g = true :=
      Finset.filter_congr fun g _ => by rw [Bool.not_eq_true]
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun g : Fin n => halfSplit n g = true)
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [hF']
    exact h
  unfold BalancedSplit
  exact ⟨by omega, by omega⟩

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
