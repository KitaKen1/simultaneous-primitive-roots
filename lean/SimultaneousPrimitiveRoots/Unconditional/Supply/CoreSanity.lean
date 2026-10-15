module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Reduction
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSided

/-!
# Sanity lemmas for the objects fed into Theorem 6.1 and Theorem 7.1

* `freePart` is idempotent, so the allocation core `allocationCore` of `Reduction.lean` (the `G_P` of
  `[P-07:0559–0565]`) satisfies the invariance half of `CoreAdmissible` by definition
  (`allocationCore_coreInvariant`), as `[P-07:0566–0568]` says.
* Degenerate instances that the statements include and that are harmless: a slot system with an
  empty slot is admissible, and then `f_x = 0`, `C_x = 0`; with no bands the marked weight is `1`.

The proofs were written by the independent reviewer of the statement layer (2026-10-12).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply

/-! ### `freePart` and the allocation core -/

theorem freePart_eq_prod (P : Finset ℕ) (n : ℕ) :
    freePart P n = (n.factorization.filter (fun p => p ∉ P)).prod (· ^ ·) := by
  unfold freePart
  rw [Finsupp.prod, Finsupp.support_filter, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpP : p ∉ P := (Finset.mem_filter.mp hp).2
  rw [Finsupp.filter_apply_pos (fun p => p ∉ P) n.factorization hpP]

theorem freePart_factorization (P : Finset ℕ) (n : ℕ) :
    (freePart P n).factorization = n.factorization.filter (fun p => p ∉ P) := by
  rw [freePart_eq_prod]
  refine Nat.prod_pow_factorization_eq_self fun p hp => ?_
  rw [Finsupp.support_filter, Finset.mem_filter, Nat.support_factorization] at hp
  exact Nat.prime_of_mem_primeFactors hp.1

theorem freePart_idem (P : Finset ℕ) (n : ℕ) : freePart P (freePart P n) = freePart P n := by
  have h : (n.factorization.filter (fun p => p ∉ P)).filter (fun p => p ∉ P) =
      n.factorization.filter (fun p => p ∉ P) := by
    ext a
    simp only [Finsupp.filter_apply]
    split_ifs <;> rfl
  rw [freePart_eq_prod P (freePart P n), freePart_factorization, h, ← freePart_eq_prod]

/-- `G_P(v) = G_P(v_*)` for the Lean allocation core. -/
theorem allocationCore_invariant (x γ : ℝ) (j : ℕ) (candidates active : Finset ℕ) (v : ℕ) :
    allocationCore x γ j candidates active (freePart active v) =
      allocationCore x γ j candidates active v := by
  unfold allocationCore
  rw [freePart_idem]

/-- The first hypothesis of `CoreAdmissible` for the allocation core of an active system. -/
theorem allocationCore_coreInvariant (𝔊 : ActiveGroups) (x γ : ℝ) (j : ℕ) (candidates : Finset ℕ) :
    ∀ n : ℕ, 0 < n →
      ((allocationCore x γ j candidates 𝔊.allPrimes n : ℝ) : ℂ) =
        ((allocationCore x γ j candidates 𝔊.allPrimes (freePart 𝔊.allPrimes n) : ℝ) : ℂ) :=
  fun n _ => by rw [allocationCore_invariant]

/-! ### Degenerate instances -/

theorem slotTuples_eq_empty {d : ℕ} (S : Fin d → Finset ℕ) {i : Fin d} (hi : S i = ∅) :
    slotTuples S = ∅ := by
  unfold slotTuples
  have h : Fintype.piFinset S = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro 𝔩 h𝔩
    have h1 := Fintype.mem_piFinset.mp h𝔩 i
    rw [hi] at h1
    exact Finset.notMem_empty _ h1
  rw [h]
  simp

theorem slotCount_eq_zero_of_empty_slot {d : ℕ} (S : Fin d → Finset ℕ) {i : Fin d}
    (hi : S i = ∅) (u : ℕ) : slotCount S u = 0 := by
  unfold slotCount
  rw [slotTuples_eq_empty S hi]
  simp

theorem slotMass_eq_zero_of_empty_slot {d : ℕ} (S : Fin d → Finset ℕ) {i : Fin d}
    (hi : S i = ∅) : slotMass S = 0 := by
  unfold slotMass
  rw [slotTuples_eq_empty S hi]
  simp

/-- With one empty slot the system is admissible whatever the upper ends of the other slots. -/
theorem slotsAdmissible_of_empty_slot {d : ℕ} {ε x : ℝ} (hx : 0 ≤ x) (S : Fin d → Finset ℕ)
    {i : Fin d} (hi : S i = ∅) (hprime : ∀ i, ∀ ℓ ∈ S i, ℓ.Prime)
    (hint : ∀ i, ∀ ℓ₁ ∈ S i, ∀ ℓ₂ ∈ S i, ∀ ℓ : ℕ, ℓ.Prime → ℓ₁ ≤ ℓ → ℓ ≤ ℓ₂ → ℓ ∈ S i)
    (hlow : ∀ i, ∀ ℓ ∈ S i, x ^ ε ≤ (ℓ : ℝ)) : SlotsAdmissible ε x S where
  prime := hprime
  interval := hint
  lower := hlow
  upper := by
    have h0 : ∏ j, (((S j).sup id : ℕ) : ℝ) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi]; simp)
    rw [h0]
    exact Real.rpow_nonneg hx _

/-- With `K = 0` bands the marked weight is identically `1`. -/
theorem markedWeight_zero_bands (q : ℝ) (𝔞 : MarkingArray 0) (x : ℝ) (n : ℕ) :
    markedWeight q 𝔞 x n = 1 := by
  unfold markedWeight
  simp

end SimultaneousPrimitiveRoots.Unconditional.Supply
