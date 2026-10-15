module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Statements
public import SimultaneousPrimitiveRoots.Hooley.PrimeReciprocalWindow
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The slot statistic is bounded, for one slot

`slotBounded_one : SlotBounded 1` (`[P-07:0016–0019]`): `C_x = O_ε(1)` and `f_x(u) = O_ε(1)` for
`1 ≤ u ≤ R x`, uniformly in the admissible slots. For one slot this needs no Mertens estimate:

* `C_x ≤ ∑_{x^ε ≤ ℓ ≤ x} 1/ℓ ≤ 12 C / ε` by the Chebyshev window bound
  `prime_reciprocal_window_le` of `Hooley/PrimeReciprocalWindow.lean`;
* `f_x(u)` is the number `k` of primes `ℓ ≥ x^ε` of the slot dividing `u`; their product divides
  `u`, so `x^{εk} ≤ u ≤ R x` and `k ≤ 2/ε` once `log x ≥ log R`.

This discharges the field `slotBounded` of `ExtractionLeaves` for `d = 1` (the case needed
downstream).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter
open scoped Topology

noncomputable section

/-- A one-slot system is a constant family. -/
theorem slots_one_eq (S : Fin 1 → Finset ℕ) : S = fun _ => S 0 := by
  funext i
  exact congrArg S (Subsingleton.elim i 0)

/-- Primes `ℓ ≥ y` of a set `T` that all divide `u ≥ 1` satisfy `y^{|T|} ≤ u`. -/
theorem pow_card_le_of_primes_dvd {T : Finset ℕ} {y : ℝ} {u : ℕ} (hy : 0 ≤ y) (hu : 1 ≤ u)
    (hprime : ∀ ℓ ∈ T, ℓ.Prime) (hdvd : ∀ ℓ ∈ T, ℓ ∣ u) (hlow : ∀ ℓ ∈ T, y ≤ (ℓ : ℝ)) :
    y ^ T.card ≤ (u : ℝ) := by
  have hprod : ∏ ℓ ∈ T, ℓ ∣ u :=
    Finset.prod_primes_dvd u (fun ℓ hℓ => (hprime ℓ hℓ).prime) hdvd
  have hle : ∏ ℓ ∈ T, ℓ ≤ u := Nat.le_of_dvd hu hprod
  calc y ^ T.card = ∏ _ℓ ∈ T, y := (Finset.prod_const y).symm
    _ ≤ ∏ ℓ ∈ T, (ℓ : ℝ) := Finset.prod_le_prod (fun _ _ => hy) hlow
    _ = ((∏ ℓ ∈ T, ℓ : ℕ) : ℝ) := (Nat.cast_prod _ _).symm
    _ ≤ (u : ℝ) := by exact_mod_cast hle

/-- At most `2/ε` primes `ℓ ≥ x^ε` divide an integer `1 ≤ u ≤ R x`, once `log R ≤ log x`. -/
theorem card_le_two_div {ε R x : ℝ} (hε : 0 < ε) (hR : 0 < R) (hx : 1 < x)
    (hRx : Real.log R ≤ Real.log x) {T : Finset ℕ} {u : ℕ} (hu : 1 ≤ u)
    (hu2 : (u : ℝ) ≤ R * x) (hprime : ∀ ℓ ∈ T, ℓ.Prime) (hdvd : ∀ ℓ ∈ T, ℓ ∣ u)
    (hlow : ∀ ℓ ∈ T, x ^ ε ≤ (ℓ : ℝ)) : (T.card : ℝ) ≤ 2 / ε := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have hxε : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 ε
  have h1 : (x ^ ε) ^ T.card ≤ R * x :=
    (pow_card_le_of_primes_dvd hxε.le hu hprime hdvd hlow).trans hu2
  have h2 : Real.log ((x ^ ε) ^ T.card) ≤ Real.log (R * x) :=
    Real.log_le_log (pow_pos hxε _) h1
  rw [Real.log_pow, Real.log_rpow hx0, Real.log_mul hR.ne' hx0.ne'] at h2
  have h3 : (T.card : ℝ) * ε * Real.log x ≤ 2 * Real.log x := by linarith
  have h4 : (T.card : ℝ) * ε ≤ 2 := le_of_mul_le_mul_right h3 hL
  exact (le_div_iff₀ hε).mpr h4

/-- `∑_{ℓ ∈ S} 1/ℓ ≤ 12 C / ε` for a set `S` of primes in `[x^ε, x]`, with a Chebyshev constant
`C` valid from `N`, once `x^ε ≥ N + 3`, `ε log x ≥ 2` and `log x ≥ 1`. -/
theorem reciprocalMass_le_of_window {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hπ : ∀ n : ℕ, N ≤ n → (Nat.primeCounting n : ℝ) ≤ C * n / Real.log n)
    {ε x : ℝ} (hε : 0 < ε) (hx : 1 < x) (hbig : (N : ℝ) + 3 ≤ x ^ ε)
    (hεL : 2 ≤ ε * Real.log x) (hL1 : 1 ≤ Real.log x) {S : Finset ℕ}
    (hprime : ∀ ℓ ∈ S, ℓ.Prime) (hlow : ∀ ℓ ∈ S, x ^ ε ≤ (ℓ : ℝ))
    (hup : ∀ ℓ ∈ S, (ℓ : ℝ) ≤ x) : reciprocalMass S ≤ 12 * C / ε := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := by linarith
  have hceil : x ^ ε ≤ (⌈x ^ ε⌉₊ : ℝ) := Nat.le_ceil _
  have hceil3 : N + 3 ≤ ⌈x ^ ε⌉₊ := by exact_mod_cast hbig.trans hceil
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a + 1 = ⌈x ^ ε⌉₊ := ⟨⌈x ^ ε⌉₊ - 1, by omega⟩
  have hNa : N ≤ a := by omega
  have ha2 : 2 ≤ a := by omega
  have haR : x ^ ε - 1 ≤ (a : ℝ) := by
    have h : ((a + 1 : ℕ) : ℝ) = (⌈x ^ ε⌉₊ : ℝ) := by rw [ha]
    rw [Nat.cast_add, Nat.cast_one] at h
    linarith
  have hsub : S ⊆ (Finset.Ioc a ⌊x⌋₊).filter Nat.Prime := by
    intro ℓ hℓ
    have h1 : ⌈x ^ ε⌉₊ ≤ ℓ := Nat.ceil_le.mpr (hlow ℓ hℓ)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨by omega, Nat.le_floor (hup ℓ hℓ)⟩, hprime ℓ hℓ⟩
  have hwin := prime_reciprocal_window_le hC hπ hNa ha2 (b := ⌊x⌋₊)
  have hmass : reciprocalMass S ≤
      ∑ q ∈ (Finset.Ioc a ⌊x⌋₊).filter Nat.Prime, (1 / (q : ℝ)) := by
    unfold reciprocalMass
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => by positivity
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hxε2 : 2 ≤ x ^ ε := by linarith
  have hxεpos : 0 < x ^ ε := by linarith
  have ha_ge : x ^ ε / 2 ≤ (a : ℝ) := by linarith
  have hloga : ε * Real.log x / 2 ≤ Real.log (a : ℝ) := by
    have h1 : Real.log (x ^ ε / 2) ≤ Real.log (a : ℝ) :=
      Real.log_le_log (by linarith) ha_ge
    rw [Real.log_div hxεpos.ne' two_ne_zero, Real.log_rpow hx0] at h1
    have h2 : Real.log 2 ≤ 1 := by
      have h := Real.log_two_lt_d9
      linarith
    linarith
  have hloga0 : 0 < ε * Real.log x / 2 := by linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hnatlog : (Nat.log 2 (⌊x⌋₊ / a) : ℝ) ≤ 2 * Real.log x := by
    rcases Nat.eq_zero_or_pos (⌊x⌋₊ / a) with h0 | hpos
    · rw [h0, Nat.log_zero_right, Nat.cast_zero]
      linarith
    · have h1 := natLog_two_le_log_div hpos.ne'
      have hm_le : ((⌊x⌋₊ / a : ℕ) : ℝ) ≤ x := by
        have h2 : ⌊x⌋₊ / a ≤ ⌊x⌋₊ := Nat.div_le_self _ _
        calc ((⌊x⌋₊ / a : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h2
          _ ≤ x := Nat.floor_le hx0.le
      have hmpos : (0 : ℝ) < ((⌊x⌋₊ / a : ℕ) : ℝ) := by exact_mod_cast hpos
      have hlogm : Real.log ((⌊x⌋₊ / a : ℕ) : ℝ) ≤ Real.log x := Real.log_le_log hmpos hm_le
      calc (Nat.log 2 (⌊x⌋₊ / a) : ℝ) ≤ Real.log ((⌊x⌋₊ / a : ℕ) : ℝ) / Real.log 2 := h1
        _ ≤ Real.log x / Real.log 2 := div_le_div_of_nonneg_right hlogm (by linarith)
        _ ≤ Real.log x / (1 / 2) := div_le_div_of_nonneg_left hL.le (by norm_num) hlog2
        _ = 2 * Real.log x := by ring
  have hC2 : 0 ≤ 2 * C := by linarith
  have hfac : 0 ≤ 2 * C / (ε * Real.log x / 2) := div_nonneg hC2 hloga0.le
  have hcount : 0 ≤ (Nat.log 2 (⌊x⌋₊ / a) : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ (Nat.log 2 (⌊x⌋₊ / a) : ℝ) := Nat.cast_nonneg _
    linarith
  calc reciprocalMass S ≤ ∑ q ∈ (Finset.Ioc a ⌊x⌋₊).filter Nat.Prime, (1 / (q : ℝ)) := hmass
    _ ≤ 2 * C / Real.log (a : ℝ) * ((Nat.log 2 (⌊x⌋₊ / a) : ℝ) + 1) := hwin
    _ ≤ 2 * C / (ε * Real.log x / 2) * (3 * Real.log x) :=
        mul_le_mul (div_le_div_of_nonneg_left hC2 hloga0 hloga) (by linarith) hcount hfac
    _ = 12 * C / ε := by
        rw [div_mul_eq_mul_div, div_eq_div_iff hloga0.ne' hε.ne']
        ring

/-- **The slot statistic is bounded, for one slot** (`[P-07:0016–0019]`), from Chebyshev's
bound. -/
theorem slotBounded_one : SlotBounded 1 := by
  intro ε hε R hR
  obtain ⟨C, hC0, N, hπ⟩ := exists_chebyshev_constant
  refine ⟨max (12 * C / ε) (2 / ε), ?_⟩
  have h1 : ∀ᶠ x : ℝ in atTop, (N : ℝ) + 3 ≤ x ^ ε :=
    (tendsto_rpow_atTop hε).eventually_ge_atTop _
  have h2 : ∀ᶠ x : ℝ in atTop, max (2 / ε) (max 1 (Real.log R)) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  filter_upwards [h1, h2, eventually_gt_atTop (1 : ℝ)] with x hx1 hx2 hx3 S hS
  have hLε : 2 / ε ≤ Real.log x := (le_max_left _ _).trans hx2
  have hL1 : 1 ≤ Real.log x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx2
  have hLR : Real.log R ≤ Real.log x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx2
  have hεL : 2 ≤ ε * Real.log x := by
    rw [mul_comm]
    exact (div_le_iff₀ hε).mp hLε
  have hS0 : S = fun _ => S 0 := slots_one_eq S
  have hprime : ∀ ℓ ∈ S 0, ℓ.Prime := hS.prime 0
  have hlow : ∀ ℓ ∈ S 0, x ^ ε ≤ (ℓ : ℝ) := hS.lower 0
  have hup : ∀ ℓ ∈ S 0, (ℓ : ℝ) ≤ x := by
    intro ℓ hℓ
    have h := hS.upper
    rw [Fin.prod_univ_one] at h
    have hsup : ℓ ≤ (S 0).sup id := Finset.le_sup (f := id) hℓ
    have h3 : x ^ (1 - ε) ≤ x :=
      calc x ^ (1 - ε) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx3.le (by linarith)
        _ = x := Real.rpow_one x
    calc (ℓ : ℝ) ≤ (((S 0).sup id : ℕ) : ℝ) := by exact_mod_cast hsup
      _ ≤ x ^ (1 - ε) := h
      _ ≤ x := h3
  constructor
  · rw [hS0, slotMass_one]
    exact (reciprocalMass_le_of_window hC0 hπ hε hx3 hx1 hεL hL1 hprime hlow hup).trans
      (le_max_left _ _)
  · intro u hu1 hu2
    rw [hS0, slotCount_one]
    unfold primeHits
    refine (card_le_two_div hε hR hx3 hLR hu1 hu2 ?_ ?_ ?_).trans (le_max_right _ _)
    · intro ℓ hℓ
      exact hprime ℓ (Finset.mem_filter.mp hℓ).1
    · intro ℓ hℓ
      exact (Finset.mem_filter.mp hℓ).2
    · intro ℓ hℓ
      exact hlow ℓ (Finset.mem_filter.mp hℓ).1

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
