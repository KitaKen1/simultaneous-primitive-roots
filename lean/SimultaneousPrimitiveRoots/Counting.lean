module

public import SimultaneousPrimitiveRoots.Statement
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Tactic

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots

open Filter

theorem positiveDyadicLowerBound_of_eventually {A : Finset ℕ} {c : ℝ}
    (hc : 0 < c)
    (h : ∀ᶠ x : ℝ in atTop, c * (x / Real.log x) ≤ primeCount A x) :
    PositiveDyadicLowerBound A := by
  obtain ⟨y, hy⟩ := eventually_atTop.mp h
  exact ⟨c, hc, max 2 y, le_max_left _ _, fun x hx => hy x ((le_max_right _ _).trans hx)⟩

/-- The final subtraction step. The two analytic bounds remain explicit hypotheses. -/
theorem positiveDyadicLowerBound_of_supply_and_exceptions
    {A : Finset ℕ} {supply exceptions : ℝ → ℝ} {κ ε : ℝ}
    (hgap : ε < κ)
    (hcapture : ∀ᶠ x : ℝ in atTop, supply x - exceptions x ≤ primeCount A x)
    (hsupply : ∀ᶠ x : ℝ in atTop, κ * (x / Real.log x) ≤ supply x)
    (hexceptions : ∀ᶠ x : ℝ in atTop, exceptions x ≤ ε * (x / Real.log x)) :
    PositiveDyadicLowerBound A := by
  apply positiveDyadicLowerBound_of_eventually (sub_pos.mpr hgap)
  filter_upwards [hcapture, hsupply, hexceptions] with x hc hs he
  nlinarith

def badCandidates (A C : Finset ℕ) : Finset ℕ := by
  classical
  exact C.filter fun p => ¬ SimultaneousAt A p

theorem candidates_card_le {A C : Finset ℕ} {x : ℝ}
    (hC : ∀ p ∈ C, x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x) :
    C.card ≤ (goodPrimes A x).card + (badCandidates A C).card := by
  classical
  have hsub : C.filter (SimultaneousAt A) ⊆ goodPrimes A x := by
    intro p hp
    obtain ⟨hpC, hpGood⟩ := Finset.mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := hC p hpC
    simp only [goodPrimes, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_iff.mpr (Nat.le_floor hhi), hlo, hhi, hpGood⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := C) (p := SimultaneousAt A)
  have hle := Finset.card_le_card hsub
  unfold badCandidates
  omega

theorem candidates_sub_bad_le_primeCount {A C : Finset ℕ} {x : ℝ}
    (hC : ∀ p ∈ C, x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x) :
    (C.card : ℝ) - (badCandidates A C).card ≤ primeCount A x := by
  have h := candidates_card_le (A := A) hC
  have hreal : (C.card : ℝ) ≤ (goodPrimes A x).card + (badCandidates A C).card := by
    exact_mod_cast h
  unfold primeCount
  linarith

end SimultaneousPrimitiveRoots
