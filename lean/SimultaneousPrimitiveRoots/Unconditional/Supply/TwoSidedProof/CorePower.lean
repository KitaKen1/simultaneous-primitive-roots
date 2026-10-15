module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.SlotBound

/-!
# The centered core is bounded on power ranges, for one slot

`corePowerBounded_one`: for one slot, `CorePowerBounded 1` (`[P-06:0079–0082]`) follows from the
boundedness of the array weight, `Extraction.ArrayWeightBounded q` for every `0 < q < 1`
(`[P-07:0043–0045]`, a leaf of the decomposition of [P] §7 in `Supply/Extraction/`, where it is
derived from Mertens' estimate). So the leaf `corePower` of `OpenLeaves 1 H 𝔅` reduces to that
leaf; it is not a hypothesis of the chain.

* "The harmonic prime estimates give `C_x = O_ε(1)`": for one slot `C_x ≤ ∑_{x^ε ≤ ℓ ≤ x} 1/ℓ ≤
  12 C / ε` by the Chebyshev window bound `Extraction.reciprocalMass_le_of_window`.
* "On every fixed positive-power range for `n`, there are only `O_ε(1)` prime divisors in the slot
  ranges": the primes `ℓ ≥ x^ε` of the slot dividing `1 ≤ u ≤ x^κ` have product at most `u`, so
  their number is at most `κ/ε` (`card_le_div_of_le_rpow`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open Filter
open scoped Topology

/-- At most `κ/ε` primes `ℓ ≥ x^ε` divide an integer `1 ≤ u ≤ x^κ`. -/
theorem card_le_div_of_le_rpow {ε κ x : ℝ} (hε : 0 < ε) (hx : 1 < x) {T : Finset ℕ} {u : ℕ}
    (hu : 1 ≤ u) (hu2 : (u : ℝ) ≤ x ^ κ) (hprime : ∀ ℓ ∈ T, ℓ.Prime) (hdvd : ∀ ℓ ∈ T, ℓ ∣ u)
    (hlow : ∀ ℓ ∈ T, x ^ ε ≤ (ℓ : ℝ)) : (T.card : ℝ) ≤ κ / ε := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have hxε : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 ε
  have h1 : (x ^ ε) ^ T.card ≤ x ^ κ :=
    (Extraction.pow_card_le_of_primes_dvd hxε.le hu hprime hdvd hlow).trans hu2
  have h2 : Real.log ((x ^ ε) ^ T.card) ≤ Real.log (x ^ κ) :=
    Real.log_le_log (pow_pos hxε _) h1
  rw [Real.log_pow, Real.log_rpow hx0, Real.log_rpow hx0] at h2
  have h3 : (T.card : ℝ) * ε * Real.log x ≤ κ * Real.log x := by linarith
  have h4 : (T.card : ℝ) * ε ≤ κ := le_of_mul_le_mul_right h3 hL
  exact (le_div_iff₀ hε).mpr h4

/-- **`F_x` is bounded on `1 ≤ u ≤ x^κ`, for one slot**, given the boundedness of the array
weight. The bound is `max(C_W, 0) · max(12 C/ε, κ/ε)` with `C_W` the bound of `𝒲` and `C` a
Chebyshev constant. -/
theorem corePowerBounded_one
    (hW : ∀ q : ℝ, 0 < q → q < 1 → Extraction.ArrayWeightBounded q) : CorePowerBounded 1 := by
  intro q hq hq1 ε hε κ hκ K
  obtain ⟨C, hC0, N, hπ⟩ := exists_chebyshev_constant
  obtain ⟨CW, hCW⟩ := hW q hq hq1 K
  refine ⟨max CW 0 * max (12 * C / ε) (κ / ε),
    mul_nonneg (le_max_right _ _) (le_trans (div_nonneg hκ.le hε.le) (le_max_right _ _)),
    fun 𝔞 => ?_⟩
  have h1 : ∀ᶠ x : ℝ in atTop, (N : ℝ) + 3 ≤ x ^ ε :=
    (tendsto_rpow_atTop hε).eventually_ge_atTop _
  have h2 : ∀ᶠ x : ℝ in atTop, max (2 / ε) 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp
    (((hCW 𝔞).and h1).and (h2.and (eventually_gt_atTop (1 : ℝ))))
  refine ⟨x₀, fun x hx S hS u hu1 hu2 => ?_⟩
  obtain ⟨⟨hx2, hx1⟩, hx3, hx4⟩ := hx₀ x hx
  have hLε : 2 / ε ≤ Real.log x := (le_max_left _ _).trans hx3
  have hL1 : 1 ≤ Real.log x := (le_max_right _ _).trans hx3
  have hεL : 2 ≤ ε * Real.log x := by
    rw [mul_comm]
    exact (div_le_iff₀ hε).mp hLε
  have hS0 : S = fun _ => S 0 := Extraction.slots_one_eq S
  have hprime : ∀ ℓ ∈ S 0, ℓ.Prime := hS.prime 0
  have hlow : ∀ ℓ ∈ S 0, x ^ ε ≤ (ℓ : ℝ) := hS.lower 0
  have hup : ∀ ℓ ∈ S 0, (ℓ : ℝ) ≤ x := by
    intro ℓ hℓ
    have h := hS.upper
    rw [Fin.prod_univ_one] at h
    have hsup : ℓ ≤ (S 0).sup id := Finset.le_sup (f := id) hℓ
    have h3 : x ^ (1 - ε) ≤ x :=
      calc x ^ (1 - ε) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx4.le (by linarith)
        _ = x := Real.rpow_one x
    calc (ℓ : ℝ) ≤ (((S 0).sup id : ℕ) : ℝ) := by exact_mod_cast hsup
      _ ≤ x ^ (1 - ε) := h
      _ ≤ x := h3
  have hmass : slotMass S ≤ 12 * C / ε := by
    rw [hS0, slotMass_one]
    exact Extraction.reciprocalMass_le_of_window hC0 hπ hε hx4 hx1 hεL hL1 hprime hlow hup
  have hcount : (slotCount S u : ℝ) ≤ κ / ε := by
    rw [hS0, slotCount_one]
    unfold primeHits
    refine card_le_div_of_le_rpow hε hx4 hu1 hu2 ?_ ?_ ?_
    · intro ℓ hℓ
      exact hprime ℓ (Finset.mem_filter.mp hℓ).1
    · intro ℓ hℓ
      exact (Finset.mem_filter.mp hℓ).2
    · intro ℓ hℓ
      exact hlow ℓ (Finset.mem_filter.mp hℓ).1
  have hw : |markedWeight q 𝔞 x u| ≤ max CW 0 := (hx2 u).trans (le_max_left _ _)
  have hc0 : (0 : ℝ) ≤ (slotCount S u : ℝ) := Nat.cast_nonneg _
  have hm0 : 0 ≤ slotMass S := by
    unfold slotMass
    exact Finset.sum_nonneg fun 𝔩 _ => by positivity
  have hdiff : |(slotCount S u : ℝ) - slotMass S| ≤ max (12 * C / ε) (κ / ε) := by
    rw [abs_le]
    constructor
    · linarith [le_max_left (12 * C / ε) (κ / ε)]
    · linarith [le_max_right (12 * C / ε) (κ / ε)]
  unfold centeredCore
  rw [abs_mul]
  exact mul_le_mul hw hdiff (abs_nonneg _) (le_max_right _ _)

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
