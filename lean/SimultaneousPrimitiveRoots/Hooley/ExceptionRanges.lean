module

public import SimultaneousPrimitiveRoots.Hooley.ResiduePrimes
public import SimultaneousPrimitiveRoots.Hooley.PrimeReciprocalWindow
public import SimultaneousPrimitiveRoots.CandidateSets
public import SimultaneousPrimitiveRoots.SplittingTail
public import SimultaneousPrimitiveRoots.RealProgressionSieve

/-!
# Hooley's three ranges for the obstruction prime

A candidate prime `p ∈ (x, 2x]` in the chosen residue classes that fails to have every base as
a primitive root has an obstruction prime `q > Y` with `q ∣ p - 1` and `a^((p-1)/q) = 1`.
Following Hooley, `q` falls in one of three ranges:

* `q ≤ √x / log⁴ x`: the splitting estimate `GRHSplittingBound` (a consequence of GRH);
* `√x / log⁴ x < q ≤ √x log² x`: the unconditional Selberg sieve bound for `p ≡ 1 (mod q)`;
* `q > √x log² x`: then `ord_p(a) ≤ 2 √x / log² x`, a small-order exception.

This file proves the classification and the pointwise cardinality bounds. The candidate supply
`progressionCandidates` needs no factorization of `p - 1`, so no supply hypothesis is used.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Finset
noncomputable section
open Classical

/-- **GRH-strength splitting estimate for the base `a`.** For every prime `q > a`, the primes
`p ∈ (x, 2x]` with `q ∣ p - 1` and `a^((p-1)/q) = 1` number at most
`C x / (q (q - 1) log x) + C √x log² (q x)`.

Under the generalized Riemann hypothesis for the Dedekind zeta functions of the Kummer fields
`ℚ(ζ_q, a^(1/q))` this holds with a constant `C` depending only on `a` (Hooley 1967; the
effective Chebotarev theorem of Lagarias–Odlyzko 1977 with Serre's refinement 1981). It is an
explicit hypothesis here and is not proved. -/
def GRHSplittingBound (a : ℕ) (C : ℝ) : Prop :=
  ∀ q : ℕ, q.Prime → a < q → ∀ x : ℝ, 2 ≤ x →
    ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
      C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
        C * Real.sqrt x * Real.log ((q : ℝ) * x) ^ 2

theorem GRHSplittingBound.mono {a : ℕ} {C C' : ℝ} (h : GRHSplittingBound a C)
    (hCC : C ≤ C') : GRHSplittingBound a C' := by
  intro q hq haq x hx
  have hb := h q hq haq x hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have h1 : 0 ≤ (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) := by
    apply mul_nonneg (div_nonneg (by linarith) hlog.le)
    apply div_nonneg zero_le_one
    nlinarith
  have h2 : 0 ≤ Real.sqrt x * Real.log ((q : ℝ) * x) ^ 2 := by positivity
  have e1 : C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
      C * Real.sqrt x * Real.log ((q : ℝ) * x) ^ 2 =
        C * ((x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1)))) +
          C * (Real.sqrt x * Real.log ((q : ℝ) * x) ^ 2) := by ring
  have e2 : C' * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
      C' * Real.sqrt x * Real.log ((q : ℝ) * x) ^ 2 =
        C' * ((x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1)))) +
          C' * (Real.sqrt x * Real.log ((q : ℝ) * x) ^ 2) := by ring
  rw [e1] at hb
  rw [e2]
  exact hb.trans (add_le_add (mul_le_mul_of_nonneg_right hCC h1)
    (mul_le_mul_of_nonneg_right hCC h2))

/-- End of the GRH range: `√x / log⁴ x`. -/
def grhCutoff (x : ℝ) : ℕ := ⌊Real.sqrt x / Real.log x ^ 4⌋₊

/-- Start of the small-order range: `√x log² x`. -/
def orderCutoff (x : ℝ) : ℕ := ⌊Real.sqrt x * Real.log x ^ 2⌋₊

/-- The order threshold `2 √x / log² x`. -/
def smallOrderCutoff (x : ℝ) : ℕ := ⌊2 * Real.sqrt x / Real.log x ^ 2⌋₊

/-- The right side of the splitting estimate is monotone in its constant. -/
theorem splittingRHS_mono {C C' x : ℝ} {q : ℕ} (hq : q.Prime) (hx : 2 ≤ x) (hCC : C ≤ C') :
    C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
        C * Real.sqrt x * Real.log ((q : ℝ) * x) ^ 2 ≤
      C' * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
        C' * Real.sqrt x * Real.log ((q : ℝ) * x) ^ 2 := by
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have h1 : 0 ≤ (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) := by
    apply mul_nonneg (div_nonneg (by linarith) hlog.le)
    apply div_nonneg zero_le_one
    nlinarith
  have h2 : 0 ≤ Real.sqrt x * Real.log ((q : ℝ) * x) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hCC h1, mul_le_mul_of_nonneg_right hCC h2]

/-- The splitting estimate of `GRHSplittingBound`, required only for large `x` and only for
`q ≤ √x / log⁴ x`, the range used by Hooley's method. -/
def GRHSplittingBoundUpTo (a : ℕ) (C : ℝ) : Prop :=
  ∀ᶠ x : ℝ in Filter.atTop, ∀ q : ℕ, q.Prime → a < q → q ≤ grhCutoff x →
    ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
      C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
        C * Real.sqrt x * Real.log ((q : ℝ) * x) ^ 2

theorem GRHSplittingBound.upTo {a : ℕ} {C : ℝ} (h : GRHSplittingBound a C) :
    GRHSplittingBoundUpTo a C := by
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
  intro q hq haq _
  exact h q hq haq x hx

theorem GRHSplittingBoundUpTo.mono {a : ℕ} {C C' : ℝ} (h : GRHSplittingBoundUpTo a C)
    (hCC : C ≤ C') : GRHSplittingBoundUpTo a C' := by
  filter_upwards [h, Filter.eventually_ge_atTop (2 : ℝ)] with x hx hx2
  intro q hq haq hcut
  exact (hx q hq haq hcut).trans (splittingRHS_mono hq hx2 hCC)

/-- Exceptions whose obstruction prime lies in `(Y, √x / log⁴ x]`. -/
def grhRangeExceptions (A : Finset ℕ) (Y : ℕ) (x : ℝ) : Finset ℕ :=
  A.biUnion fun a => ((Ioc Y (grhCutoff x)).filter Nat.Prime).biUnion fun q =>
    powerResidueExceptionPrimes a q x

/-- Primes `p ≤ 2x` with `p ≡ 1 (mod q)` for a prime `q ∈ (√x / log⁴ x, √x log² x]`. -/
def windowExceptions (x : ℝ) : Finset ℕ :=
  ((Ioc (grhCutoff x) (orderCutoff x)).filter Nat.Prime).biUnion fun q =>
    progressionPrefixPrimes q (⌊2 * x⌋₊ + 1)

/-- Primes in `(x, 2x]` at which `a` has order at most `2 √x / log² x`. -/
def smallOrderPrimesAt (a : ℕ) (x : ℝ) : Finset ℕ :=
  (range (⌊2 * x⌋₊ + 1)).filter fun p =>
    p.Prime ∧ x < (p : ℝ) ∧ p ∣ smallOrderProduct a (smallOrderCutoff x)

/-- Small-order exceptions for some base of `A`. -/
def smallOrderAt (A : Finset ℕ) (x : ℝ) : Finset ℕ :=
  A.biUnion fun a => smallOrderPrimesAt a x

/-- Past `√x log² x`, the cofactor `(p - 1) / q` is below the small-order threshold. -/
theorem quotient_le_smallOrderCutoff {x : ℝ} (hx : 1 < x) {p q : ℕ} (hp : (p : ℝ) ≤ 2 * x)
    (hq : orderCutoff x < q) : (p - 1) / q ≤ smallOrderCutoff x := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hqreal : Real.sqrt x * Real.log x ^ 2 < q := by
    have hfl := Nat.lt_floor_add_one (Real.sqrt x * Real.log x ^ 2)
    have hq' : (orderCutoff x : ℝ) + 1 ≤ q := by exact_mod_cast hq
    unfold orderCutoff at hq'
    linarith
  have hqpos : (0 : ℝ) < q := lt_of_le_of_lt (by positivity) hqreal
  apply Nat.le_floor
  have h1 : (((p - 1) / q : ℕ) : ℝ) ≤ (p : ℝ) / q := by
    rw [le_div_iff₀ hqpos]
    have hle : (p - 1) / q * q ≤ p := (Nat.div_mul_le_self (p - 1) q).trans (Nat.sub_le p 1)
    exact_mod_cast hle
  have h2 : (p : ℝ) / q ≤ 2 * x / q := div_le_div_of_nonneg_right hp hqpos.le
  have h3 : 2 * x / q ≤ 2 * Real.sqrt x / Real.log x ^ 2 := by
    rw [div_le_div_iff₀ hqpos (by positivity)]
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
    nlinarith
  linarith

/-- **Hooley's classification.** A failed candidate falls in one of the three ranges. -/
theorem bad_progressionCandidates_subset {A : Finset ℕ} {Y H : ℕ} {R : Finset ℕ} {x : ℝ}
    (hpos : ∀ a ∈ A, 2 ≤ a) (hx : 3 ≤ x) (hR : ProgressionConditions A Y H R) :
    badCandidates A (progressionCandidates H R x) ⊆
      smallOrderAt A x ∪ grhRangeExceptions A Y x ∪ windowExceptions x := by
  intro p hp
  obtain ⟨hpC, hpbad⟩ := Finset.mem_filter.mp hp
  obtain ⟨hprange, hpprime, hpx, hp2x, u, hu, hpu⟩ := Finset.mem_filter.mp hpC
  have hp3 : 3 < p := by
    have hcast : (3 : ℝ) < (p : ℝ) := hx.trans_lt hpx
    exact_mod_cast hcast
  obtain ⟨hsq, havoid⟩ := hR u hu p hpprime hp3 hpu
  have hf : ¬ ∀ a ∈ A, PrimitiveRootMod a p := fun hall => hpbad ⟨hpprime, hall⟩
  push Not at hf
  obtain ⟨a, haA, hafail⟩ := hf
  have ha : ¬ p ∣ a := nonsquare_natCast_not_dvd (hsq a haA)
  obtain ⟨q, hq, hqp, hpow⟩ := exists_prime_obstruction hpprime ha hafail
  have havoid' : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≤ Y → ¬ q ∣ p - 1 := by
    intro q hq hq2 hqY
    exact havoid q hq (by have := hq.two_le; omega) hqY
  have hqY : Y < q := by
    by_contra hle
    exact small_prime_tests hpprime (by omega) ha (hsq a haA) havoid' q hq hqp (by omega) hpow
  by_cases h1 : q ≤ grhCutoff x
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨a, haA, Finset.mem_biUnion.mpr ⟨q, ?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hqY, h1⟩, hq⟩
    · exact Finset.mem_filter.mpr ⟨hprange, hpprime, hpx, hp2x, ha, hqp, hpow⟩
  · by_cases h2 : q ≤ orderCutoff x
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, h2⟩, hq⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨hprange, hpprime, hqp⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨a, haA, Finset.mem_filter.mpr ⟨hprange, hpprime, hpx, ?_⟩⟩
      have hjpos : 1 ≤ (p - 1) / q := Nat.div_pos (Nat.le_of_dvd (by omega) hqp) hq.pos
      have hjle := quotient_le_smallOrderCutoff (by linarith) hp2x (by omega : orderCutoff x < q)
      exact dvd_smallOrderProduct_of_pow_eq_one (hpos a haA) hjpos hjle hpow

/-- Small-order exceptions: at most `(∑ log a) m² / log x` with `m = 2 √x / log² x`. -/
theorem smallOrderAt_card_le {A : Finset ℕ} (hpos : ∀ a ∈ A, 2 ≤ a) {x : ℝ} (hx : 1 < x) :
    ((smallOrderAt A x).card : ℝ) ≤
      (∑ a ∈ A, Real.log a) * (smallOrderCutoff x : ℝ) ^ 2 / Real.log x := by
  calc ((smallOrderAt A x).card : ℝ) ≤ ∑ a ∈ A, ((smallOrderPrimesAt a x).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ a ∈ A, (smallOrderCutoff x : ℝ) ^ 2 * Real.log a / Real.log x := by
        apply sum_le_sum
        intro a ha
        apply small_order_exception_card_le (hpos a ha) hx
        intro p hp
        obtain ⟨_, hpp, hpx, hpd⟩ := mem_filter.mp hp
        exact ⟨hpp, hpx, hpd⟩
    _ = (∑ a ∈ A, Real.log a) * (smallOrderCutoff x : ℝ) ^ 2 / Real.log x := by
        rw [Finset.sum_mul, Finset.sum_div]
        apply sum_congr rfl
        intro a _
        ring

/-- GRH-range exceptions: the main terms sum to `C / Y`; the error terms are counted crudely. -/
theorem grhRangeExceptions_card_le {A : Finset ℕ} {Y : ℕ} {C x : ℝ} (hY : 1 ≤ Y)
    (hYbase : ∀ a ∈ A, a ≤ Y) (hC : 0 ≤ C) (hx : 3 ≤ x)
    (hGRH : ∀ a ∈ A, ∀ q : ℕ, q.Prime → a < q → q ≤ grhCutoff x →
      ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
        C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
          C * Real.sqrt x * Real.log ((q : ℝ) * x) ^ 2) :
    ((grhRangeExceptions A Y x).card : ℝ) ≤
      (A.card : ℝ) * (C / Y * (x / Real.log x) +
        C * (grhCutoff x : ℝ) * (Real.sqrt x * Real.log ((grhCutoff x : ℝ) * x) ^ 2)) := by
  set S := (Ioc Y (grhCutoff x)).filter Nat.Prime with hS
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hscale : 0 ≤ C * (x / Real.log x) := mul_nonneg hC (div_nonneg (by linarith) hlog.le)
  have hSmem : ∀ q ∈ S, q.Prime ∧ Y < q ∧ q ≤ grhCutoff x := by
    intro q hq
    obtain ⟨hqI, hqp⟩ := mem_filter.mp hq
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hqI
    exact ⟨hqp, h1, h2⟩
  have hScard : (S.card : ℝ) ≤ grhCutoff x := by
    have h : S.card ≤ grhCutoff x := by
      calc S.card ≤ (Ioc Y (grhCutoff x)).card := card_filter_le _ _
        _ = grhCutoff x - Y := Nat.card_Ioc _ _
        _ ≤ grhCutoff x := Nat.sub_le _ _
    exact_mod_cast h
  have hper : ∀ a ∈ A, (((S.biUnion fun q => powerResidueExceptionPrimes a q x).card : ℝ)) ≤
      C / Y * (x / Real.log x) +
        C * (grhCutoff x : ℝ) * (Real.sqrt x * Real.log ((grhCutoff x : ℝ) * x) ^ 2) := by
    intro a ha
    have hterm : ∀ q ∈ S, ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
        C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
          C * (Real.sqrt x * Real.log ((grhCutoff x : ℝ) * x) ^ 2) := by
      intro q hq
      obtain ⟨hqp, hqY, hqX⟩ := hSmem q hq
      have hb := hGRH a ha q hqp ((hYbase a ha).trans_lt hqY) hqX
      have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hqp.two_le
      have hqX' : (q : ℝ) ≤ grhCutoff x := by exact_mod_cast hqX
      have hpos1 : 0 ≤ Real.log ((q : ℝ) * x) := Real.log_nonneg (by nlinarith)
      have hmono : Real.log ((q : ℝ) * x) ≤ Real.log ((grhCutoff x : ℝ) * x) :=
        Real.log_le_log (by positivity) (by nlinarith)
      have hsq : Real.log ((q : ℝ) * x) ^ 2 ≤ Real.log ((grhCutoff x : ℝ) * x) ^ 2 :=
        pow_le_pow_left₀ hpos1 hmono 2
      have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
      calc ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
            C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
              C * Real.sqrt x * Real.log ((q : ℝ) * x) ^ 2 := hb
        _ ≤ C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
              C * (Real.sqrt x * Real.log ((grhCutoff x : ℝ) * x) ^ 2) := by
            have h' : C * Real.sqrt x * Real.log ((q : ℝ) * x) ^ 2 ≤
                C * (Real.sqrt x * Real.log ((grhCutoff x : ℝ) * x) ^ 2) := by
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hsqrt) hC
            linarith
    have htail := reciprocal_tail_finset_le hY S (fun q hq => (hSmem q hq).2.1)
    have herr : 0 ≤ C * (Real.sqrt x * Real.log ((grhCutoff x : ℝ) * x) ^ 2) := by positivity
    calc (((S.biUnion fun q => powerResidueExceptionPrimes a q x).card : ℝ))
        ≤ ∑ q ∈ S, ((powerResidueExceptionPrimes a q x).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ q ∈ S, (C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
            C * (Real.sqrt x * Real.log ((grhCutoff x : ℝ) * x) ^ 2)) := sum_le_sum hterm
      _ = C * (x / Real.log x) * (∑ q ∈ S, 1 / ((q : ℝ) * ((q : ℝ) - 1))) +
            (S.card : ℝ) * (C * (Real.sqrt x * Real.log ((grhCutoff x : ℝ) * x) ^ 2)) := by
          rw [sum_add_distrib, ← Finset.mul_sum, sum_const, nsmul_eq_mul]
      _ ≤ C * (x / Real.log x) * (1 / (Y : ℝ)) +
            (grhCutoff x : ℝ) * (C * (Real.sqrt x * Real.log ((grhCutoff x : ℝ) * x) ^ 2)) :=
          add_le_add (mul_le_mul_of_nonneg_left htail hscale)
            (mul_le_mul_of_nonneg_right hScard herr)
      _ = C / Y * (x / Real.log x) +
            C * (grhCutoff x : ℝ) * (Real.sqrt x * Real.log ((grhCutoff x : ℝ) * x) ^ 2) := by
          ring
  calc ((grhRangeExceptions A Y x).card : ℝ) ≤
        ∑ a ∈ A, (((S.biUnion fun q => powerResidueExceptionPrimes a q x).card : ℝ)) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ _a ∈ A, (C / Y * (x / Real.log x) +
        C * (grhCutoff x : ℝ) * (Real.sqrt x * Real.log ((grhCutoff x : ℝ) * x) ^ 2)) :=
        sum_le_sum hper
    _ = _ := by rw [sum_const, nsmul_eq_mul]

/-- Window exceptions: the Selberg sieve bound for `p ≡ 1 (mod q)` at level `y = x^(1/8)`. -/
theorem windowExceptions_card_le {x : ℝ} (hx : 1 < x) :
    ((windowExceptions x).card : ℝ) ≤
      4 * ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ) / Real.log (x ^ (1 / 8 : ℝ)) *
          (∑ q ∈ (Ioc (grhCutoff x) (orderCutoff x)).filter Nat.Prime, (1 / (q : ℝ))) +
        (orderCutoff x : ℝ) * (x ^ (1 / 8 : ℝ) * (1 + Real.log (x ^ (1 / 8 : ℝ))) ^ 3 +
          x ^ (1 / 8 : ℝ) + 2) := by
  set W := (Ioc (grhCutoff x) (orderCutoff x)).filter Nat.Prime with hW
  set y := x ^ (1 / 8 : ℝ) with hy
  set N := ⌊2 * x⌋₊ + 1 with hN
  have hy1 : 1 < y := Real.one_lt_rpow hx (by norm_num)
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hE : 0 ≤ y * (1 + Real.log y) ^ 3 + y + 2 := by positivity
  have hWcard : (W.card : ℝ) ≤ orderCutoff x := by
    have h : W.card ≤ orderCutoff x := by
      calc W.card ≤ (Ioc (grhCutoff x) (orderCutoff x)).card := card_filter_le _ _
        _ = orderCutoff x - grhCutoff x := Nat.card_Ioc _ _
        _ ≤ orderCutoff x := Nat.sub_le _ _
    exact_mod_cast h
  calc ((windowExceptions x).card : ℝ) ≤
        ∑ q ∈ W, ((progressionPrefixPrimes q N).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ q ∈ W, (4 * (N : ℝ) / ((q : ℝ) * Real.log y) +
          (y * (1 + Real.log y) ^ 3 + y + 2)) := by
        apply sum_le_sum
        intro q hq
        have hqp := (mem_filter.mp hq).2
        have h := progressionPrefixPrimes_card_real_sieve_le hqp y N hy1
        linarith
    _ = 4 * (N : ℝ) / Real.log y * (∑ q ∈ W, (1 / (q : ℝ))) +
          (W.card : ℝ) * (y * (1 + Real.log y) ^ 3 + y + 2) := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, Finset.mul_sum]
        congr 1
        apply sum_congr rfl
        intro q _
        field_simp
    _ ≤ 4 * (N : ℝ) / Real.log y * (∑ q ∈ W, (1 / (q : ℝ))) +
          (orderCutoff x : ℝ) * (y * (1 + Real.log y) ^ 3 + y + 2) := by
        linarith [mul_le_mul_of_nonneg_right hWcard hE]

end
end SimultaneousPrimitiveRoots
