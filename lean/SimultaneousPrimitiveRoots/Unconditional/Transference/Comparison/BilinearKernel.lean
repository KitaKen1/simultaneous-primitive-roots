module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Leaves
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The geometric-sum kernel of the integer bilinear estimate

Source: `verification/stage7-sources/S-03.tex`, lines 128–158 (`[S-03:0128–0158]`), the proof of
[S] Lemma 4.2. This file contains the analytic part; the blocks and the assembly are in
`Comparison/BilinearBlocks.lean` and `Comparison/IntegerBilinear.lean`.

* `Bilinear.geomKernel N L θ = |∑_{N ≤ n < N + L} e(θ n)|`, the geometric sum over the full
  containing interval. "The geometric-sum bound on the full interval of `n`" is
  `geomKernel_le` (`≤ L`) and `geomKernel_mul_fract_le` (`≤ 1 / (2 x (1 - x))`, `x` the
  fractional part of `θ`; this is the bound `min{U, ‖θ‖⁻¹}` of the paper up to a constant, since
  `x (1 - x) ≥ ‖θ‖ / 2`). The second one follows from `|e(θ) - 1| = 2 sin(π x) ≥ 4 x (1 - x)`
  (`chord_ge`, Jordan's inequality).
* `Bilinear.binWeight L r m` — the bound attached to the `m`-th of the `2r` arcs of length
  `1/(2r)` of the circle: `L` for the arc at the origin, `r / m` otherwise ("ordering them by
  distance from zero"). `le_binWeight_add`: a phase in the arc `m = ⌊2 r x⌋` contributes at most
  the weights of `m` and of the reflected arc `2r - 1 - m`. `sum_binWeight_le`: the weights add
  up to at most `L + r (1 + log(2r))`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Bilinear

/-! ### The phase `e(t)` -/

theorem expUnit_zero : expUnit 0 = 1 := by
  unfold expUnit
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]

theorem expUnit_add (x y : ℝ) : expUnit (x + y) = expUnit x * expUnit y := by
  unfold expUnit
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `e(-x)` is the conjugate of `e(x)`. -/
theorem expUnit_neg (x : ℝ) : expUnit (-x) = conj (expUnit x) := by
  have h1 : expUnit (-x) * expUnit x = 1 := by
    rw [← expUnit_add, neg_add_cancel, expUnit_zero]
  have h2 : conj (expUnit x) * expUnit x = 1 := by
    rw [Complex.conj_mul', norm_expUnit, Complex.ofReal_one, one_pow]
  have h3 : expUnit x ≠ 0 := by
    intro h
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  exact mul_right_cancel₀ h3 (h1.trans h2.symm)

theorem expUnit_mul_natCast (θ : ℝ) (n : ℕ) : expUnit (θ * (n : ℝ)) = expUnit θ ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, mul_zero, expUnit_zero, pow_zero]
  | succ n ih =>
    have h : θ * ((n + 1 : ℕ) : ℝ) = θ * (n : ℝ) + θ := by
      rw [Nat.cast_add_one]
      ring
    rw [h, expUnit_add, ih, pow_succ]

/-- `e(t + m) = e(t)` for an integer `m`. -/
theorem expUnit_add_intCast (t : ℝ) (m : ℤ) : expUnit (t + (m : ℝ)) = expUnit t := by
  unfold expUnit
  have h : (2 * Real.pi * Complex.I * ((t + (m : ℝ) : ℝ) : ℂ)) =
      2 * Real.pi * Complex.I * (t : ℂ) + (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `e(θ)` depends only on the fractional part of `θ`. -/
theorem expUnit_fract (θ : ℝ) : expUnit (Int.fract θ) = expUnit θ := by
  have h := expUnit_add_intCast (Int.fract θ) ⌊θ⌋
  rw [Int.fract_add_floor] at h
  exact h.symm

/-! ### The geometric sum -/

/-- The geometric sum `|∑_{N ≤ n < N + L} e(θ n)|` over an interval of `L` integers. -/
def geomKernel (N L : ℕ) (θ : ℝ) : ℝ :=
  ‖∑ n ∈ Finset.Ico N (N + L), expUnit (θ * (n : ℝ))‖

theorem geomKernel_nonneg (N L : ℕ) (θ : ℝ) : 0 ≤ geomKernel N L θ := norm_nonneg _

/-- The trivial bound: the number of terms. -/
theorem geomKernel_le (N L : ℕ) (θ : ℝ) : geomKernel N L θ ≤ (L : ℝ) := by
  unfold geomKernel
  calc ‖∑ n ∈ Finset.Ico N (N + L), expUnit (θ * (n : ℝ))‖
      ≤ ∑ n ∈ Finset.Ico N (N + L), ‖expUnit (θ * (n : ℝ))‖ := norm_sum_le _ _
    _ = ∑ _n ∈ Finset.Ico N (N + L), (1 : ℝ) :=
        Finset.sum_congr rfl fun n _ => norm_expUnit _
    _ = (L : ℝ) := by
        rw [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul, mul_one]

/-- The geometric-sum bound: `|∑ e(θ n)| · |e(θ) - 1| ≤ 2`. -/
theorem geomKernel_mul_chord_le (N L : ℕ) (θ : ℝ) :
    geomKernel N L θ * ‖expUnit θ - 1‖ ≤ 2 := by
  have h1 : (∑ n ∈ Finset.Ico N (N + L), expUnit (θ * (n : ℝ))) * (expUnit θ - 1) =
      expUnit θ ^ (N + L) - expUnit θ ^ N := by
    rw [Finset.sum_congr rfl fun n _ => expUnit_mul_natCast θ n]
    exact geom_sum_Ico_mul _ (Nat.le_add_right N L)
  unfold geomKernel
  rw [← norm_mul, h1]
  calc ‖expUnit θ ^ (N + L) - expUnit θ ^ N‖
      ≤ ‖expUnit θ ^ (N + L)‖ + ‖expUnit θ ^ N‖ := norm_sub_le _ _
    _ = 2 := by
        rw [norm_pow, norm_pow, norm_expUnit, one_pow, one_pow]
        exact one_add_one_eq_two

/-- `sin(π x) ≥ 2 x (1 - x)` on `[0, 1]` (Jordan's inequality on each half). -/
theorem two_mul_le_sin_pi {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    2 * (x * (1 - x)) ≤ Real.sin (Real.pi * x) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hcancel : ∀ y : ℝ, 2 / Real.pi * (Real.pi * y) = 2 * y := by
    intro y
    calc 2 / Real.pi * (Real.pi * y) = 2 * y * (Real.pi / Real.pi) := by ring
      _ = 2 * y := by rw [div_self hπ.ne', mul_one]
  rcases le_total x (1 / 2) with h | h
  · have hle : Real.pi * x ≤ Real.pi / 2 := by
      have h' := mul_le_mul_of_nonneg_left h hπ.le
      linarith
    have h1 := Real.mul_le_sin (mul_nonneg hπ.le hx0) hle
    rw [hcancel] at h1
    have h2 : 0 ≤ x * x := mul_nonneg hx0 hx0
    nlinarith
  · have h0 : 0 ≤ 1 - x := by linarith
    have hle : Real.pi * (1 - x) ≤ Real.pi / 2 := by
      have h' := mul_le_mul_of_nonneg_left (show 1 - x ≤ 1 / 2 by linarith) hπ.le
      linarith
    have h1 := Real.mul_le_sin (mul_nonneg hπ.le h0) hle
    have h3 : Real.pi * (1 - x) = Real.pi - Real.pi * x := by ring
    rw [hcancel, h3, Real.sin_pi_sub] at h1
    have h2 : 0 ≤ (1 - x) * (1 - x) := mul_nonneg h0 h0
    nlinarith

/-- The chord `|e(θ) - 1|` is at least `4 x (1 - x)`, `x` the fractional part of `θ`. -/
theorem chord_ge (θ : ℝ) :
    4 * (Int.fract θ * (1 - Int.fract θ)) ≤ ‖expUnit θ - 1‖ := by
  have h1 : ‖expUnit (Int.fract θ) - 1‖ = ‖2 * Real.sin (Real.pi * Int.fract θ)‖ := by
    have h := Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * Int.fract θ)
    have he : expUnit (Int.fract θ) =
        Complex.exp (Complex.I * ((2 * Real.pi * Int.fract θ : ℝ) : ℂ)) := by
      unfold expUnit
      congr 1
      push_cast
      ring
    have hs : 2 * Real.pi * Int.fract θ / 2 = Real.pi * Int.fract θ := by ring
    rw [he, h, hs]
  have h2 := two_mul_le_sin_pi (Int.fract_nonneg θ) (Int.fract_lt_one θ).le
  have h3 : 2 * Real.sin (Real.pi * Int.fract θ) ≤ |2 * Real.sin (Real.pi * Int.fract θ)| :=
    le_abs_self _
  rw [← expUnit_fract, h1, Real.norm_eq_abs]
  linarith

/-- The geometric sum is at most `1 / (2 x (1 - x))`, `x` the fractional part of `θ`. -/
theorem geomKernel_mul_fract_le (N L : ℕ) (θ : ℝ) :
    geomKernel N L θ * (2 * (Int.fract θ * (1 - Int.fract θ))) ≤ 1 := by
  have h1 := geomKernel_mul_chord_le N L θ
  have h3 := mul_le_mul_of_nonneg_left (chord_ge θ) (geomKernel_nonneg N L θ)
  nlinarith

/-! ### The weights of the arcs -/

/-- The bound attached to the `m`-th arc of length `1/(2r)`: the length `L` of the interval for
the arc at the origin, and `r / m` for the arc at distance `m/(2r)` from the origin. -/
def binWeight (L : ℝ) (r m : ℕ) : ℝ := if m = 0 then L else (r : ℝ) / (m : ℝ)

theorem binWeight_zero (L : ℝ) (r : ℕ) : binWeight L r 0 = L := by
  unfold binWeight
  exact if_pos rfl

theorem binWeight_of_ne_zero (L : ℝ) (r : ℕ) {m : ℕ} (hm : m ≠ 0) :
    binWeight L r m = (r : ℝ) / (m : ℝ) := by
  unfold binWeight
  exact if_neg hm

theorem binWeight_nonneg {L : ℝ} (hL : 0 ≤ L) (r m : ℕ) : 0 ≤ binWeight L r m := by
  unfold binWeight
  split_ifs
  · exact hL
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- A value `Γ ≤ L` with `Γ · 2x(1-x) ≤ 1`, `x < 1`, is at most the sum of the weights of the arc
`m` containing `x` (`m ≤ 2 r x < m + 1`) and of the reflected arc `2r - 1 - m`. -/
theorem le_binWeight_add {L Γ x : ℝ} {r m : ℕ} (hr : 0 < r) (hΓ0 : 0 ≤ Γ) (hΓL : Γ ≤ L)
    (hx1 : x < 1) (hΓx : Γ * (2 * (x * (1 - x))) ≤ 1)
    (hm_le : (m : ℝ) ≤ 2 * (r : ℝ) * x) (hm_lt : 2 * (r : ℝ) * x < (m : ℝ) + 1) :
    m < 2 * r ∧ Γ ≤ binWeight L r m + binWeight L r (2 * r - 1 - m) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hL : 0 ≤ L := hΓ0.trans hΓL
  have hm2r : m < 2 * r := by
    have h2 : 2 * (r : ℝ) * x < 2 * (r : ℝ) * 1 :=
      mul_lt_mul_of_pos_left hx1 (mul_pos two_pos hrpos)
    have h : (m : ℝ) < 2 * (r : ℝ) := by linarith
    exact_mod_cast h
  refine ⟨hm2r, ?_⟩
  have hcast : ((2 * r - 1 - m : ℕ) : ℝ) = 2 * (r : ℝ) - 1 - (m : ℝ) := by
    have h : 2 * r - 1 - m + m + 1 = 2 * r := by omega
    have h' : ((2 * r - 1 - m : ℕ) : ℝ) + (m : ℝ) + 1 = 2 * (r : ℝ) := by exact_mod_cast h
    linarith
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have h := binWeight_nonneg hL r (2 * r - 1 - m)
    rw [hm0, binWeight_zero]
    rw [hm0] at h
    linarith
  rcases Nat.eq_zero_or_pos (2 * r - 1 - m) with hm0' | hmpos'
  · have h := binWeight_nonneg hL r m
    rw [hm0', binWeight_zero]
    linarith
  · rw [binWeight_of_ne_zero L r hmpos.ne', binWeight_of_ne_zero L r hmpos'.ne', hcast]
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
    have hm1' : (1 : ℝ) ≤ 2 * (r : ℝ) - 1 - (m : ℝ) := by
      rw [← hcast]
      exact_mod_cast hmpos'
    have hb' : 2 * (r : ℝ) - 1 - (m : ℝ) ≤ 2 * (r : ℝ) * (1 - x) := by linarith
    have ha : 0 < 2 * (r : ℝ) * x := by linarith
    have hb : 0 < 2 * (r : ℝ) * (1 - x) := by linarith
    have hab : 0 < (2 * (r : ℝ) * x) * (2 * (r : ℝ) * (1 - x)) := mul_pos ha hb
    have h1 : Γ * ((2 * (r : ℝ) * x) * (2 * (r : ℝ) * (1 - x))) ≤ 2 * (r : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hΓx
        (mul_nonneg zero_le_two (sq_nonneg (r : ℝ)))
      calc Γ * ((2 * (r : ℝ) * x) * (2 * (r : ℝ) * (1 - x)))
          = Γ * (2 * (x * (1 - x))) * (2 * (r : ℝ) ^ 2) := by ring
        _ ≤ 1 * (2 * (r : ℝ) ^ 2) := h
        _ = 2 * (r : ℝ) ^ 2 := one_mul _
    have h2 : Γ ≤ (r : ℝ) / (2 * (r : ℝ) * x) + (r : ℝ) / (2 * (r : ℝ) * (1 - x)) := by
      rw [div_add_div _ _ ha.ne' hb.ne', le_div_iff₀ hab]
      calc Γ * ((2 * (r : ℝ) * x) * (2 * (r : ℝ) * (1 - x))) ≤ 2 * (r : ℝ) ^ 2 := h1
        _ = (r : ℝ) * (2 * (r : ℝ) * (1 - x)) + (2 * (r : ℝ) * x) * (r : ℝ) := by ring
    have h3 : (r : ℝ) / (2 * (r : ℝ) * x) ≤ (r : ℝ) / (m : ℝ) :=
      div_le_div_of_nonneg_left hrpos.le (by linarith) hm_le
    have h4 : (r : ℝ) / (2 * (r : ℝ) * (1 - x)) ≤ (r : ℝ) / (2 * (r : ℝ) - 1 - (m : ℝ)) :=
      div_le_div_of_nonneg_left hrpos.le (by linarith) hb'
    linarith

/-- The harmonic sum: `∑_{i < n} 1/(i + 1) ≤ 1 + log n`. -/
theorem sum_inv_le_one_add_log (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℝ) + 1)⁻¹ ≤ 1 + Real.log (n : ℝ) := by
  have h := harmonic_le_one_add_log n
  have h3 : ((harmonic n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, ((i : ℝ) + 1)⁻¹ := by
    rw [harmonic, Rat.cast_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Rat.cast_inv, Rat.cast_natCast, Nat.cast_add_one]
  rw [h3] at h
  exact h

/-- The weights of all `2r` arcs add up to at most `L + r (1 + log(2r))`
("`O(U + ∑_{1 ≤ j ≤ 2r} r/j) = O(U + r log(2r))`"). -/
theorem sum_binWeight_le {L : ℝ} {r : ℕ} (hr : 0 < r) :
    ∑ m ∈ Finset.range (2 * r), binWeight L r m ≤
      L + (r : ℝ) * (1 + Real.log (2 * (r : ℝ))) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 2 * r = n + 1 := ⟨2 * r - 1, by omega⟩
  have hn' : (n : ℝ) + 1 = 2 * (r : ℝ) := by exact_mod_cast hn.symm
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : ∀ i ∈ Finset.range n, binWeight L r (i + 1) = (r : ℝ) * ((i : ℝ) + 1)⁻¹ := by
    intro i _
    rw [binWeight_of_ne_zero L r (Nat.add_one_ne_zero i), div_eq_mul_inv, Nat.cast_add_one]
  have h4 : Real.log (n : ℝ) ≤ Real.log (2 * (r : ℝ)) := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by linarith)
    · exact Real.log_le_log (Nat.cast_pos.mpr hpos) (by linarith)
  have h5 : (r : ℝ) * ∑ i ∈ Finset.range n, ((i : ℝ) + 1)⁻¹ ≤
      (r : ℝ) * (1 + Real.log (2 * (r : ℝ))) :=
    mul_le_mul_of_nonneg_left (by linarith [sum_inv_le_one_add_log n]) (Nat.cast_nonneg r)
  rw [hn, Finset.sum_range_succ', binWeight_zero, Finset.sum_congr rfl h1, ← Finset.mul_sum]
  linarith

end Bilinear

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
