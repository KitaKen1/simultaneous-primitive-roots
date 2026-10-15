module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.SlotBound

/-!
# `C_x = O_ε(1)` for every number of slots

`slotMassBounded d : SlotMassBounded d` (`[P-06:0079]`: "The harmonic prime estimates give
`C_x = O_ε(1)`"), for every `d`; `slotMassBounded_one` (`EndpointProof/SlotMass.lean`) is the case
`d = 1`.

* `slotMass_le_prod_reciprocalMass`: dropping the condition that the slot primes are distinct,
  `C_x = ∑_𝔩 1 / (ℓ_1 ⋯ ℓ_d) ≤ ∏_i ∑_{ℓ ∈ S_i} 1/ℓ`.
* If some slot is empty there is no tuple and `C_x = 0`. Otherwise every slot has upper endpoint
  `≥ 1`, so each upper endpoint is at most the product of all of them, which is `≤ x^{1-ε} ≤ x`;
  then each slot is a set of primes of `[x^ε, x]` and `∑_{ℓ ∈ S_i} 1/ℓ ≤ 12 C / ε` by the
  Chebyshev window bound (`Extraction.reciprocalMass_le_of_window`).

The bound is `max(1, 12 C / ε)^d`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology

noncomputable section

/-- `C_x ≤ ∏_i V_{S_i}`: the tuples with distinct entries are among all tuples. -/
theorem slotMass_le_prod_reciprocalMass {d : ℕ} (S : Fin d → Finset ℕ) :
    slotMass S ≤ ∏ i, reciprocalMass (S i) := by
  have hsub : slotTuples S ⊆ Fintype.piFinset S := by
    unfold slotTuples
    exact Finset.filter_subset _ _
  have hterm : ∀ 𝔩 : Fin d → ℕ, 1 / ((∏ i, 𝔩 i : ℕ) : ℝ) = ∏ i, 1 / ((𝔩 i : ℕ) : ℝ) := by
    intro 𝔩
    rw [Nat.cast_prod, Finset.prod_div_distrib, Finset.prod_const_one]
  unfold slotMass reciprocalMass
  calc ∑ 𝔩 ∈ slotTuples S, 1 / ((∏ i, 𝔩 i : ℕ) : ℝ)
      ≤ ∑ 𝔩 ∈ Fintype.piFinset S, 1 / ((∏ i, 𝔩 i : ℕ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun 𝔩 _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _))
    _ = ∑ 𝔩 ∈ Fintype.piFinset S, ∏ i, 1 / ((𝔩 i : ℕ) : ℝ) :=
        Finset.sum_congr rfl fun 𝔩 _ => hterm 𝔩
    _ = ∏ i, ∑ ℓ ∈ S i, 1 / (ℓ : ℝ) :=
        (Finset.prod_univ_sum S fun _ ℓ => 1 / (ℓ : ℝ)).symm

/-- **`C_x = O_ε(1)`** (`[P-06:0079]`), for every number of slots, uniformly in the admissible
slot systems. -/
theorem slotMassBounded (d : ℕ) : SlotMassBounded d := by
  intro ε hε
  obtain ⟨C, hC0, N, hπ⟩ := exists_chebyshev_constant
  have h1 : ∀ᶠ x : ℝ in atTop, (N : ℝ) + 3 ≤ x ^ ε :=
    (tendsto_rpow_atTop hε).eventually_ge_atTop _
  have h2 : ∀ᶠ x : ℝ in atTop, max (2 / ε) 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  obtain ⟨x₀, hx₀⟩ :=
    Filter.eventually_atTop.mp (h1.and (h2.and (eventually_gt_atTop (1 : ℝ))))
  refine ⟨max 1 (12 * C / ε) ^ d, x₀, ?_⟩
  intro x hx S hS
  obtain ⟨hbig, hlog, hx1⟩ := hx₀ x hx
  have hLε : 2 / ε ≤ Real.log x := (le_max_left _ _).trans hlog
  have hL1 : 1 ≤ Real.log x := (le_max_right _ _).trans hlog
  have hεL : 2 ≤ ε * Real.log x := by
    rw [mul_comm]
    exact (div_le_iff₀ hε).mp hLε
  have hB0 : 0 ≤ max 1 (12 * C / ε) ^ d := pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  by_cases hne : ∀ i, (S i).Nonempty
  · -- every slot is nonempty: every slot prime is at most `x`
    have hsup1 : ∀ j, (1 : ℝ) ≤ (((S j).sup id : ℕ) : ℝ) := by
      intro j
      obtain ⟨ℓ, hℓ⟩ := hne j
      have h3 : 2 ≤ ℓ := (hS.prime j ℓ hℓ).two_le
      have h4 : ℓ ≤ (S j).sup id := Finset.le_sup (f := id) hℓ
      have h5 : 1 ≤ (S j).sup id := by omega
      exact_mod_cast h5
    have hup : ∀ i, ∀ ℓ ∈ S i, (ℓ : ℝ) ≤ x := by
      intro i ℓ hℓ
      have h4 : ℓ ≤ (S i).sup id := Finset.le_sup (f := id) hℓ
      have h6 : (1 : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, (((S j).sup id : ℕ) : ℝ) :=
        calc (1 : ℝ) = ∏ _j ∈ Finset.univ.erase i, (1 : ℝ) := Finset.prod_const_one.symm
          _ ≤ ∏ j ∈ Finset.univ.erase i, (((S j).sup id : ℕ) : ℝ) :=
              Finset.prod_le_prod (fun _ _ => zero_le_one) (fun j _ => hsup1 j)
      have h5 : (((S i).sup id : ℕ) : ℝ) ≤ ∏ j, (((S j).sup id : ℕ) : ℝ) :=
        calc (((S i).sup id : ℕ) : ℝ)
            ≤ (((S i).sup id : ℕ) : ℝ) *
                ∏ j ∈ Finset.univ.erase i, (((S j).sup id : ℕ) : ℝ) :=
              le_mul_of_one_le_right (Nat.cast_nonneg _) h6
          _ = ∏ j, (((S j).sup id : ℕ) : ℝ) :=
              Finset.mul_prod_erase Finset.univ (fun j => (((S j).sup id : ℕ) : ℝ))
                (Finset.mem_univ i)
      have h7 : x ^ (1 - ε) ≤ x :=
        calc x ^ (1 - ε) ≤ x ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
          _ = x := Real.rpow_one x
      calc (ℓ : ℝ) ≤ (((S i).sup id : ℕ) : ℝ) := Nat.cast_le.mpr h4
        _ ≤ ∏ j, (((S j).sup id : ℕ) : ℝ) := h5
        _ ≤ x ^ (1 - ε) := hS.upper
        _ ≤ x := h7
    have hmass : ∀ i, reciprocalMass (S i) ≤ max 1 (12 * C / ε) := fun i =>
      (Extraction.reciprocalMass_le_of_window hC0 hπ hε hx1 hbig hεL hL1 (hS.prime i)
        (hS.lower i) (hup i)).trans (le_max_right _ _)
    have hmass0 : ∀ i, 0 ≤ reciprocalMass (S i) := by
      intro i
      unfold reciprocalMass
      exact Finset.sum_nonneg fun p _ => div_nonneg zero_le_one (Nat.cast_nonneg _)
    calc slotMass S ≤ ∏ i, reciprocalMass (S i) := slotMass_le_prod_reciprocalMass S
      _ ≤ ∏ _i : Fin d, max 1 (12 * C / ε) :=
          Finset.prod_le_prod (fun i _ => hmass0 i) (fun i _ => hmass i)
      _ = max 1 (12 * C / ε) ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · -- an empty slot: there is no tuple
    obtain ⟨i, hi⟩ := not_forall.mp hne
    have hempty : S i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hi
    have h0 : slotMass S = 0 := by
      unfold slotMass
      refine Finset.sum_eq_zero fun 𝔩 h𝔩 => ?_
      exfalso
      have h3 : 𝔩 ∈ Fintype.piFinset S := by
        unfold slotTuples at h𝔩
        exact (Finset.mem_filter.mp h𝔩).1
      have h4 : 𝔩 i ∈ S i := Fintype.mem_piFinset.mp h3 i
      rw [hempty] at h4
      exact absurd h4 (Finset.notMem_empty _)
    rw [h0]
    exact hB0

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
