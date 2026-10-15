module

public import SimultaneousPrimitiveRoots.ZetaQuotientCenter
public import SimultaneousPrimitiveRoots.KummerQuotientZeroInputs
public import SimultaneousPrimitiveRoots.CyclotomicRadicals
public import Mathlib.NumberTheory.Cyclotomic.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField Metric Classical
noncomputable section

theorem kummerFullQuotientContinuation_log_norm_two_lower {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    {H : ℂ → ℂ} (hH : NumberFieldFullQuotientContinuation
      (PrimeKummerField a q) (CyclotomicField q ℚ) H) :
    -(4 * ((q : ℝ) - 1)) ≤ Real.log ‖H 2‖ := by
  let : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have h := numberFieldFullQuotientContinuation_log_norm_two_lower
    (PrimeKummerField a q) (CyclotomicField q ℚ) hH
  simpa only [prime_cyclotomic_degree (E := CyclotomicField q ℚ) (Fact.out : q.Prime),
    Nat.cast_sub (Fact.out : q.Prime).one_lt.le, Nat.cast_one] using h

theorem kummerEntireFullQuotientContinuation_jensen_degree_le {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {r R M : ℝ} (hr : 0 < |r|) (hrR : |r| < |R|) (hM : 1 ≤ M)
    (hb : ∀ z ∈ sphere (2 : ℂ) |R|, ‖H z‖ ≤ M) :
    (((∑ᶠ s : ℂ, if s ∈ closedBall (2 : ℂ) |r|
      then (fullQuotientZeroMultiplicity H s : ℤ) else 0) : ℤ) : ℝ) ≤
        (Real.log M + 4 * ((q : ℝ) - 1)) / Real.log (R / r) := by
  let : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have h := numberFieldEntireFullQuotientContinuation_jensen_degree_le
    (PrimeKummerField a q) (CyclotomicField q ℚ) hH hr hrR hM hb
  simpa only [prime_cyclotomic_degree (E := CyclotomicField q ℚ) (Fact.out : q.Prime),
    Nat.cast_sub (Fact.out : q.Prime).one_lt.le, Nat.cast_one] using h

/-- Normalize the actual integer-multiplicity sum only once. The center cost
becomes the absolute constant four, without constructing a Hecke root. -/
theorem kummerEntireFullQuotientContinuation_jensen_normalized_le {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {r R M : ℝ} (hr : 0 < |r|) (hrR : |r| < |R|) (hM : 1 ≤ M)
    (hb : ∀ z ∈ sphere (2 : ℂ) |R|, ‖H z‖ ≤ M) :
    ((((∑ᶠ s : ℂ, if s ∈ closedBall (2 : ℂ) |r|
      then (fullQuotientZeroMultiplicity H s : ℤ) else 0) : ℤ) : ℝ) /
        ((q : ℝ) - 1)) ≤
      (Real.log M / ((q : ℝ) - 1) + 4) / Real.log (R / r) := by
  have hq : 0 < (q : ℝ) - 1 := by
    have h := (Fact.out : q.Prime).one_lt
    exact sub_pos.mpr (by exact_mod_cast h)
  have h := div_le_div_of_nonneg_right
    (kummerEntireFullQuotientContinuation_jensen_degree_le hH hr hrR hM hb) hq.le
  convert h using 1 <;> first | rfl | field_simp [hq.ne']

end
end SimultaneousPrimitiveRoots
