module

public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Counts surviving the symmetric probe constraints

[S, §3, `eq:ideal-hoeffding-fraction`]: out of all j-subsets of M slots,
retain those containing m designated probes and missing ell designated slots.
The hypotheses below explicitly express the possible cardinalities. This file
proves the exact count and falling-factorial ratio for every such cardinality,
not just bounded numerical test cases. It does not yet construct the
Hoeffding projections or prove the tensor operator estimate.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

/-- Count the same disjoint probe/excluded/subset selections in two orders. -/
theorem probe_binomial_count {M m ell j : ℕ}
    (hmj : m ≤ j) (hjM : j ≤ M) (hell : ell ≤ M - j) :
    M.choose j * j.choose m * (M - j).choose ell =
      M.choose (m + ell) * (m + ell).choose m * (M - m - ell).choose (j - m) := by
  have hsym : (M - m).choose (j - m) = (M - m).choose (M - j) := by
    have h := Nat.choose_symm (show j - m ≤ M - m by omega)
    simpa only [show M - m - (j - m) = M - j by omega] using h.symm
  have hsym' : (M - m - ell).choose (M - j - ell) =
      (M - m - ell).choose (j - m) := by
    have h := Nat.choose_symm (show j - m ≤ M - m - ell by omega)
    simpa only [show M - m - ell - (j - m) = M - j - ell by omega] using h
  calc
    _ = M.choose m * ((M - m).choose (j - m) * (M - j).choose ell) := by
      rw [Nat.choose_mul hmj]
      ring
    _ = M.choose m * ((M - m).choose ell *
        (M - m - ell).choose (M - j - ell)) := by
      rw [hsym, Nat.choose_mul hell]
    _ = M.choose m * (M - m).choose ell * (M - m - ell).choose (j - m) := by
      rw [hsym']
      ring
    _ = _ := by
      rw [Nat.choose_mul (show m ≤ m + ell by omega), Nat.add_sub_cancel_left]

/-- Division-free exact falling-factorial identity. -/
theorem probe_descFactorial_count {M m ell j : ℕ}
    (hmj : m ≤ j) (hjM : j ≤ M) (hell : ell ≤ M - j) :
    M.choose j * j.descFactorial m * (M - j).descFactorial ell =
      (M - m - ell).choose (j - m) * M.descFactorial (m + ell) := by
  have hfac : (m + ell).choose m * m.factorial * ell.factorial =
      (m + ell).factorial := by
    simpa only [Nat.add_sub_cancel_left] using
      Nat.choose_mul_factorial_mul_factorial (show m ≤ m + ell by omega)
  simp only [Nat.descFactorial_eq_factorial_mul_choose]
  calc
    _ = (M.choose j * j.choose m * (M - j).choose ell) *
        m.factorial * ell.factorial := by ring
    _ = (M.choose (m + ell) * (m + ell).choose m *
        (M - m - ell).choose (j - m)) * m.factorial * ell.factorial := by
      rw [probe_binomial_count hmj hjM hell]
    _ = (M - m - ell).choose (j - m) * M.choose (m + ell) *
        ((m + ell).choose m * m.factorial * ell.factorial) := by ring
    _ = _ := by rw [hfac]; ring

/-- The exact surviving fraction, over the reals with nonzero denominators. -/
theorem probe_hoeffding_fraction {M m ell j : ℕ}
    (hmj : m ≤ j) (hjM : j ≤ M) (hell : ell ≤ M - j) :
    ((M - m - ell).choose (j - m) : ℝ) / (M.choose j : ℝ) =
      (j.descFactorial m : ℝ) * ((M - j).descFactorial ell : ℝ) /
        (M.descFactorial (m + ell) : ℝ) := by
  have hc : (M.choose j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hjM)
  have hd : (M.descFactorial (m + ell) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.descFactorial_pos.mpr (show m + ell ≤ M by omega)).ne'
  apply (div_eq_div_iff hc hd).mpr
  have h := probe_descFactorial_count hmj hjM hell
  have h' : (M - m - ell).choose (j - m) * M.descFactorial (m + ell) =
      j.descFactorial m * (M - j).descFactorial ell * M.choose j := by
    rw [← h]
    ring
  exact_mod_cast h'

/-- With no excluded slots, the top symmetric component survives completely. -/
theorem probe_top_fraction_ell_zero {M m : ℕ} (_hm : m ≤ M) :
    ((M - m - 0).choose (M - m) : ℝ) / (M.choose M : ℝ) = 1 := by
  simp

/-- Excluding a positive number of slots kills the top component. -/
theorem probe_top_count_ell_pos {M m ell : ℕ} (hm : m ≤ M) (hell : 0 < ell)
    (hslots : m + ell ≤ M) : (M - m - ell).choose (M - m) = 0 := by
  apply Nat.choose_eq_zero_of_lt
  omega

/-- The finite product lower bound used in the denominator estimate. -/
theorem one_sub_sum_le_damping_product {α : Type*} (s : Finset α) (a : α → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hai := ha i (Finset.mem_insert_self i s)
    have has : ∀ j ∈ s, 0 ≤ a j ∧ a j ≤ 1 := fun j hj =>
      ha j (Finset.mem_insert_of_mem hj)
    have hsum : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg fun j hj => (has j hj).1
    have hmul := mul_le_mul_of_nonneg_left (ih has) (sub_nonneg.mpr hai.2)
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    nlinarith [mul_nonneg hai.1 hsum]

/-- Normalize a falling factorial as a product of damped factors. -/
theorem descFactorial_normalized_product {M k : ℕ} (hM : 0 < M) (hk : k ≤ M) :
    (M.descFactorial k : ℝ) / (M : ℝ) ^ k =
      ∏ i ∈ Finset.range k, (1 - (i : ℝ) / (M : ℝ)) := by
  have hM' : (M : ℝ) ≠ 0 := by positivity
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  rw [show (M : ℝ) ^ k = ∏ _i ∈ Finset.range k, (M : ℝ) by simp]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Nat.cast_sub (show i ≤ M from (Finset.mem_range.mp hi).le.trans hk)]
  field_simp

/-- The paper's large-slot condition leaves at least half the denominator. -/
theorem descFactorial_ge_half_pow {M k : ℕ} (hM : 0 < M) (hk : k ≤ M)
    (hsize : k * (k - 1) ≤ M) :
    (M : ℝ) ^ k / 2 ≤ (M.descFactorial k : ℝ) := by
  have hM' : 0 < (M : ℝ) := by positivity
  have hs : (∑ i ∈ Finset.range k, (i : ℝ)) * 2 ≤ (M : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast (Finset.sum_range_id_mul_two k).trans_le hsize
  have hsum : (∑ i ∈ Finset.range k, (i : ℝ) / (M : ℝ)) ≤ 1 / 2 := by
    rw [← Finset.sum_div, div_le_iff₀ hM']
    linarith
  have hprod := one_sub_sum_le_damping_product (Finset.range k)
    (fun i => (i : ℝ) / (M : ℝ)) (by
      intro i hi
      constructor
      · positivity
      · apply (div_le_one hM').mpr
        exact_mod_cast (Finset.mem_range.mp hi).le.trans hk)
  rw [← descFactorial_normalized_product hM hk] at hprod
  have hhalf : (1 / 2 : ℝ) ≤ (M.descFactorial k : ℝ) / (M : ℝ) ^ k := by
    linarith
  have h := (le_div_iff₀ (pow_pos hM' k)).mp hhalf
  linarith

/-- A combinatorial substitute for maximizing t^m(1-t)^ell by calculus. -/
theorem probe_power_bound {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (m ell : ℕ) (hm : 0 < m) :
    t ^ m * (1 - t) ^ ell ≤ (ell : ℝ) ^ ell / (m : ℝ) ^ ell := by
  have hterm : t ^ m * (1 - t) ^ ell * ((m + ell).choose m : ℝ) ≤ 1 := by
    have h := Finset.single_le_sum
      (s := Finset.range (m + ell + 1))
      (f := fun i => t ^ i * (1 - t) ^ (m + ell - i) * ((m + ell).choose i : ℝ))
      (fun i hi => by positivity) (show m ∈ Finset.range (m + ell + 1) by simp)
    rw [← add_pow] at h
    simpa using h
  have hchoose : (m : ℝ) ^ ell / (ell.factorial : ℝ) ≤
      ((m + ell).choose m : ℝ) := by
    have h := (Nat.pow_le_choose (α := ℝ) ell (m + ell))
    have hm_pow : (m : ℝ) ^ ell ≤ (m + 1 : ℕ) ^ ell := by
      exact_mod_cast Nat.pow_le_pow_left (Nat.le_succ m) ell
    rw [show m + ell + 1 - ell = m + 1 by omega] at h
    rw [← Nat.choose_symm_add (a := m) (b := ell)] at h
    exact (div_le_div_of_nonneg_right hm_pow (by positivity)).trans h
  have hfactor : (ell.factorial : ℝ) ≤ (ell : ℝ) ^ ell := by
    exact_mod_cast Nat.factorial_le_pow ell
  have hf : 0 < (ell.factorial : ℝ) := by positivity
  have hp : 0 < (m : ℝ) ^ ell := by positivity
  have htprod : 0 ≤ t ^ m * (1 - t) ^ ell := by positivity
  have hbound := (mul_le_mul_of_nonneg_left hchoose htprod).trans hterm
  rw [← mul_div_assoc, div_le_one hf] at hbound
  apply (le_div_iff₀ hp).mpr
  exact hbound.trans hfactor

/-- Uniform Hoeffding shrinkage for all admissible slot cardinalities.
The number of slots is unrestricted above; the finite tests are unnecessary. -/
theorem probe_hoeffding_fraction_le {M m ell j : ℕ}
    (hM : 0 < M) (hm : 0 < m) (hmj : m ≤ j) (hjM : j ≤ M)
    (hell : ell ≤ M - j) (hsize : (m + ell) * (m + ell - 1) ≤ M) :
    ((M - m - ell).choose (j - m) : ℝ) / (M.choose j : ℝ) ≤
      2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell := by
  rw [probe_hoeffding_fraction hmj hjM hell]
  have hM' : 0 < (M : ℝ) := by positivity
  have hden := descFactorial_ge_half_pow hM (show m + ell ≤ M by omega) hsize
  have hdenpos : 0 < (M.descFactorial (m + ell) : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (show m + ell ≤ M by omega)
  have hn1 : (j.descFactorial m : ℝ) ≤ (j : ℝ) ^ m := by
    exact_mod_cast Nat.descFactorial_le_pow j m
  have hn2 : ((M - j).descFactorial ell : ℝ) ≤ (M - j : ℕ) ^ ell := by
    exact_mod_cast Nat.descFactorial_le_pow (M - j) ell
  have hnum := mul_le_mul hn1 hn2 (by positivity) (by positivity)
  have hfirst : (j.descFactorial m : ℝ) * ((M - j).descFactorial ell : ℝ) /
      (M.descFactorial (m + ell) : ℝ) ≤
      2 * ((j : ℝ) / (M : ℝ)) ^ m * (1 - (j : ℝ) / (M : ℝ)) ^ ell := by
    have hn : 0 ≤ (j : ℝ) ^ m * (M - j : ℕ) ^ ell := by positivity
    have hsub : 1 - (j : ℝ) / (M : ℝ) = ((M : ℝ) - j) / (M : ℝ) := by
      field_simp
    calc
      _ ≤ (j : ℝ) ^ m * (M - j : ℕ) ^ ell /
          (M.descFactorial (m + ell) : ℝ) :=
        div_le_div_of_nonneg_right hnum hdenpos.le
      _ ≤ (j : ℝ) ^ m * (M - j : ℕ) ^ ell / ((M : ℝ) ^ (m + ell) / 2) :=
        div_le_div_of_nonneg_left hn (by positivity) hden
      _ = _ := by
        rw [Nat.cast_sub hjM, hsub, div_pow, div_pow, pow_add]
        field_simp
  have hb := probe_power_bound (t := (j : ℝ) / (M : ℝ))
    (by positivity) ((div_le_one hM').mpr (by exact_mod_cast hjM)) m ell hm
  calc
    _ ≤ 2 * ((j : ℝ) / (M : ℝ)) ^ m * (1 - (j : ℝ) / (M : ℝ)) ^ ell := hfirst
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
      simpa only [mul_assoc, mul_div_assoc] using h

end SimultaneousPrimitiveRoots.Unconditional.Graph
