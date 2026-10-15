module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Statements

/-!
# A weighted integral over the line from mean values on intervals

`[P-06:0530–0541]`: "The Dirichlet mean-square bound in Lemma 2.2 gives, on every dyadic time
interval of length `R`, `Y⁻² ∫_{R ≤ |t| ≤ 2R} |P_a(t)|² dt ≪ L^{C_5+1} (1 + R/Y)`. For
`T_0 = LY/H`, the tail in (cor:local-mellin) is thus at most
`Y L^{C_5+1} ∑_{r ≥ 0} (2^r L)^{-j} (1 + 2^r L/H)`, which is as small as required on choosing `j`
last."

`integral_weighted_le`: for a continuous `g ≥ 0` with `∫_T^{T+Y} g ≤ G` for every `T` (a mean
value on the intervals of length `Y`), `j ≥ 2`, `H ≥ 1` and `Λ Y ≤ H T₀`, `Λ > 0`,

`∫_ℝ (1 + H|t|/Y)^{-j} g(t) dt ≤ ∫_{-T₀}^{T₀} g + 2 G Λ^{-(j-1)}`.

Here the tail `|t| > T₀` is cut into the intervals `T₀ + nY ≤ |t| ≤ T₀ + (n+1)Y` (instead of dyadic
intervals), on which the weight is at most `Λ^{-(j-2)} / ((Λ+n)(Λ+n+1))`
(`rpow_neg_natCast_le`); these numbers have sum at most `Λ^{-(j-1)}`
(`sum_inv_mul_succ_le`, a telescoping sum). The integral over `ℝ` is the limit of the integrals
over `[-(T₀ + NY), T₀ + NY]` when the integrand is integrable; when it is not, Lean's integral is
`0` and the bound is trivial.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open Filter MeasureTheory
open scoped Topology

/-- `∑_{n < N} 1/((Λ+n)(Λ+n+1)) + 1/(Λ+N) = 1/Λ`. -/
theorem sum_inv_mul_succ_add {Λ : ℝ} (hΛ : 0 < Λ) (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / ((Λ + n) * (Λ + n + 1)) + 1 / (Λ + N) = 1 / Λ := by
  induction N with
  | zero => rw [Finset.sum_range_zero, zero_add, Nat.cast_zero, add_zero]
  | succ N ih =>
    have hu : 0 < Λ + (N : ℝ) := add_pos_of_pos_of_nonneg hΛ (Nat.cast_nonneg N)
    have hv : 0 < Λ + ((N : ℝ) + 1) := by linarith
    have h1 : 1 / ((Λ + N) * (Λ + N + 1)) + 1 / (Λ + ((N : ℝ) + 1)) = 1 / (Λ + N) := by
      have e : Λ + (N : ℝ) + 1 = Λ + ((N : ℝ) + 1) := by ring
      rw [e, div_add_div _ _ (mul_pos hu hv).ne' hv.ne',
        div_eq_div_iff (mul_pos (mul_pos hu hv) hv).ne' hu.ne']
      ring
    rw [Finset.sum_range_succ, Nat.cast_add_one, add_assoc, h1]
    exact ih

/-- `∑_{n < N} 1/((Λ+n)(Λ+n+1)) ≤ 1/Λ`. -/
theorem sum_inv_mul_succ_le {Λ : ℝ} (hΛ : 0 < Λ) (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / ((Λ + n) * (Λ + n + 1)) ≤ 1 / Λ := by
  have h := sum_inv_mul_succ_add hΛ N
  have hpos : 0 ≤ 1 / (Λ + (N : ℝ)) :=
    div_nonneg zero_le_one (add_pos_of_pos_of_nonneg hΛ (Nat.cast_nonneg N)).le
  linarith

/-- `b^{-j} ≤ Λ^{-(j-2)} / ((Λ+n)(Λ+n+1))` for `b ≥ 1 + Λ + n`, `j ≥ 2`. -/
theorem rpow_neg_natCast_le {j : ℕ} (hj : 2 ≤ j) {Λ b : ℝ} {n : ℕ} (hΛ : 0 < Λ)
    (hb : 1 + Λ + n ≤ b) :
    b ^ (-(j : ℝ)) ≤ (Λ ^ (j - 2))⁻¹ * (1 / ((Λ + n) * (Λ + n + 1))) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hb0 : 0 < b := by linarith
  have hΛb : Λ ≤ b := by linarith
  have h1 : Λ ^ (j - 2) ≤ b ^ (j - 2) := pow_le_pow_left₀ hΛ.le hΛb _
  have h2 : (Λ + n) * (Λ + n + 1) ≤ b ^ 2 := by
    rw [sq]
    exact mul_le_mul (by linarith) (by linarith) (by linarith) hb0.le
  have h3 : b ^ j = b ^ (j - 2) * b ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hj]
  have hX : 0 < (Λ + n) * (Λ + n + 1) := mul_pos (by linarith) (by linarith)
  have hpos : 0 < Λ ^ (j - 2) * ((Λ + n) * (Λ + n + 1)) := mul_pos (pow_pos hΛ _) hX
  have h4 : Λ ^ (j - 2) * ((Λ + n) * (Λ + n + 1)) ≤ b ^ j := by
    rw [h3]
    exact mul_le_mul h1 h2 hX.le (pow_nonneg hb0.le _)
  rw [Real.rpow_neg hb0.le, Real.rpow_natCast, one_div, ← mul_inv]
  exact inv_anti₀ hpos h4

/-- **The tail on one side**: if `f ≤ ω_n g` on `[T₀ + nY, ∞)` and `∫_T^{T+Y} g ≤ G` for all `T`,
then `∫_{T₀}^{T₀ + NY} f ≤ G ∑_{n < N} ω_n`. -/
theorem integral_tail_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) {T₀ Y G : ℝ}
    (hY : 0 ≤ Y) (ω : ℕ → ℝ) (hω : ∀ n, 0 ≤ ω n)
    (hfg : ∀ (n : ℕ) (t : ℝ), T₀ + n * Y ≤ t → f t ≤ ω n * g t)
    (hG : ∀ T : ℝ, ∫ t in T..(T + Y), g t ≤ G) (N : ℕ) :
    ∫ t in T₀..(T₀ + N * Y), f t ≤ G * ∑ n ∈ Finset.range N, ω n := by
  have hsum : ∑ k ∈ Finset.range N,
        ∫ t in (T₀ + (k : ℝ) * Y)..(T₀ + ((k + 1 : ℕ) : ℝ) * Y), f t =
      ∫ t in (T₀ + ((0 : ℕ) : ℝ) * Y)..(T₀ + (N : ℝ) * Y), f t :=
    intervalIntegral.sum_integral_adjacent_intervals (a := fun n : ℕ => T₀ + (n : ℝ) * Y)
      fun k _ => hf.intervalIntegrable _ _
  have h0 : T₀ + ((0 : ℕ) : ℝ) * Y = T₀ := by rw [Nat.cast_zero, zero_mul, add_zero]
  rw [h0] at hsum
  rw [← hsum, Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  have hle : T₀ + (n : ℝ) * Y ≤ T₀ + ((n + 1 : ℕ) : ℝ) * Y := by
    rw [Nat.cast_add_one]
    nlinarith
  have hGn : ∫ t in (T₀ + (n : ℝ) * Y)..(T₀ + ((n + 1 : ℕ) : ℝ) * Y), g t ≤ G := by
    have h := hG (T₀ + (n : ℝ) * Y)
    have e : T₀ + (n : ℝ) * Y + Y = T₀ + ((n + 1 : ℕ) : ℝ) * Y := by
      rw [Nat.cast_add_one]
      ring
    rw [e] at h
    exact h
  calc ∫ t in (T₀ + (n : ℝ) * Y)..(T₀ + ((n + 1 : ℕ) : ℝ) * Y), f t
      ≤ ∫ t in (T₀ + (n : ℝ) * Y)..(T₀ + ((n + 1 : ℕ) : ℝ) * Y), ω n * g t :=
        intervalIntegral.integral_mono_on hle (hf.intervalIntegrable _ _)
          ((continuous_const.mul hg).intervalIntegrable _ _) fun t ht => hfg n t ht.1
    _ = ω n * ∫ t in (T₀ + (n : ℝ) * Y)..(T₀ + ((n + 1 : ℕ) : ℝ) * Y), g t :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ ω n * G := mul_le_mul_of_nonneg_left hGn (hω n)
    _ = G * ω n := mul_comm _ _

/-- **A weighted integral over the line from mean values on intervals of length `Y`.** -/
theorem integral_weighted_le {j : ℕ} (hj : 2 ≤ j) {Y H T₀ Λ G : ℝ} (hY : 0 < Y) (hH : 1 ≤ H)
    (hΛ : 0 < Λ) (hT₀ : 0 ≤ T₀) (hΛT : Λ * Y ≤ H * T₀) {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ t, 0 ≤ g t) (hG : ∀ T : ℝ, ∫ t in T..(T + Y), g t ≤ G) :
    ∫ t : ℝ, (1 + H * |t| / Y) ^ (-(j : ℝ)) * g t ≤
      (∫ t in (-T₀)..T₀, g t) + 2 * G * (Λ ^ (j - 1))⁻¹ := by
  have hG0 : 0 ≤ G :=
    (intervalIntegral.integral_nonneg (by linarith) fun t _ => hg0 t).trans (hG 0)
  have hbase : ∀ t : ℝ, 1 ≤ 1 + H * |t| / Y := fun t => by
    have h : 0 ≤ H * |t| / Y := div_nonneg (mul_nonneg (by linarith) (abs_nonneg t)) hY.le
    linarith
  have hWc : Continuous fun t : ℝ => (1 + H * |t| / Y) ^ (-(j : ℝ)) :=
    Continuous.rpow_const (by fun_prop) fun t =>
      Or.inl (lt_of_lt_of_le one_pos (hbase t)).ne'
  have hfc : Continuous fun t : ℝ => (1 + H * |t| / Y) ^ (-(j : ℝ)) * g t := hWc.mul hg
  have hW1 : ∀ t : ℝ, (1 + H * |t| / Y) ^ (-(j : ℝ)) ≤ 1 := fun t =>
    Real.rpow_le_one_of_one_le_of_nonpos (hbase t) (neg_nonpos.mpr (Nat.cast_nonneg j))
  -- the weights on `T₀ + nY ≤ |t|`
  have hω0 : ∀ n : ℕ, 0 ≤ (Λ ^ (j - 2))⁻¹ * (1 / ((Λ + n) * (Λ + n + 1))) := fun n =>
    mul_nonneg (inv_nonneg.mpr (pow_nonneg hΛ.le _))
      (div_nonneg zero_le_one (mul_nonneg
        (add_pos_of_pos_of_nonneg hΛ (Nat.cast_nonneg n)).le
        (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hΛ (Nat.cast_nonneg n))
          zero_le_one).le))
  have hweight : ∀ (n : ℕ) (t : ℝ), T₀ + n * Y ≤ |t| →
      (1 + H * |t| / Y) ^ (-(j : ℝ)) ≤ (Λ ^ (j - 2))⁻¹ * (1 / ((Λ + n) * (Λ + n + 1))) := by
    intro n t ht
    refine rpow_neg_natCast_le hj hΛ ?_
    have hnY : 0 ≤ (n : ℝ) * Y := mul_nonneg (Nat.cast_nonneg n) hY.le
    have h2 : H * (T₀ + n * Y) ≤ H * |t| := mul_le_mul_of_nonneg_left ht (by linarith)
    have h3 : (n : ℝ) * Y ≤ H * ((n : ℝ) * Y) := le_mul_of_one_le_left hnY hH
    have e : H * (T₀ + n * Y) = H * T₀ + H * ((n : ℝ) * Y) := by ring
    have h1 : Λ * Y + n * Y ≤ H * |t| := by linarith
    have h5 : Λ + n ≤ H * |t| / Y := by
      rw [le_div_iff₀ hY]
      have e2 : (Λ + n) * Y = Λ * Y + n * Y := by ring
      rw [e2]
      exact h1
    linarith
  -- the two tails
  have hpos : ∀ N : ℕ, ∫ t in T₀..(T₀ + N * Y), (1 + H * |t| / Y) ^ (-(j : ℝ)) * g t ≤
      G * ∑ n ∈ Finset.range N, (Λ ^ (j - 2))⁻¹ * (1 / ((Λ + n) * (Λ + n + 1))) := by
    intro N
    refine integral_tail_le hfc hg hY.le _ hω0 (fun n t ht => ?_) hG N
    have ht0 : 0 ≤ t :=
      le_trans (add_nonneg hT₀ (mul_nonneg (Nat.cast_nonneg n) hY.le)) ht
    have habs : |t| = t := abs_of_nonneg ht0
    exact mul_le_mul_of_nonneg_right (hweight n t (by rw [habs]; exact ht)) (hg0 t)
  have hneg : ∀ N : ℕ,
      ∫ t in (-(T₀ + N * Y))..(-T₀), (1 + H * |t| / Y) ^ (-(j : ℝ)) * g t ≤
        G * ∑ n ∈ Finset.range N, (Λ ^ (j - 2))⁻¹ * (1 / ((Λ + n) * (Λ + n + 1))) := by
    intro N
    have hcomp : ∫ t in T₀..(T₀ + N * Y), (1 + H * |(-t)| / Y) ^ (-(j : ℝ)) * g (-t) =
        ∫ t in (-(T₀ + N * Y))..(-T₀), (1 + H * |t| / Y) ^ (-(j : ℝ)) * g t :=
      intervalIntegral.integral_comp_neg (fun t => (1 + H * |t| / Y) ^ (-(j : ℝ)) * g t)
    have hfc' : Continuous fun t : ℝ => (1 + H * |(-t)| / Y) ^ (-(j : ℝ)) * g (-t) :=
      hfc.comp continuous_neg
    have hg' : Continuous fun t : ℝ => g (-t) := hg.comp continuous_neg
    rw [← hcomp]
    refine integral_tail_le hfc' hg' hY.le _ hω0 (fun n t ht => ?_) (fun T => ?_) N
    · have ht0 : 0 ≤ t :=
        le_trans (add_nonneg hT₀ (mul_nonneg (Nat.cast_nonneg n) hY.le)) ht
      have habs : |(-t)| = t := by rw [abs_neg, abs_of_nonneg ht0]
      exact mul_le_mul_of_nonneg_right (hweight n (-t) (by rw [habs]; exact ht)) (hg0 (-t))
    · have h : ∫ t in T..(T + Y), g (-t) = ∫ t in (-(T + Y))..(-T), g t :=
        intervalIntegral.integral_comp_neg g
      have h2 := hG (-(T + Y))
      have e : -(T + Y) + Y = -T := by ring
      rw [e] at h2
      rw [h]
      exact h2
  -- the sum of the weights
  have hsumω : ∀ N : ℕ,
      G * ∑ n ∈ Finset.range N, (Λ ^ (j - 2))⁻¹ * (1 / ((Λ + n) * (Λ + n + 1))) ≤
        G * (Λ ^ (j - 1))⁻¹ := by
    intro N
    refine mul_le_mul_of_nonneg_left ?_ hG0
    have h1 := sum_inv_mul_succ_le hΛ N
    have h2 : (Λ ^ (j - 2))⁻¹ * (1 / Λ) = (Λ ^ (j - 1))⁻¹ := by
      rw [one_div, ← mul_inv, ← pow_succ]
      congr 2
      omega
    rw [← Finset.mul_sum, ← h2]
    exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (pow_nonneg hΛ.le _))
  by_cases hint : Integrable fun t : ℝ => (1 + H * |t| / Y) ^ (-(j : ℝ)) * g t
  · have htop : Tendsto (fun N : ℕ => T₀ + (N : ℝ) * Y) atTop atTop :=
      tendsto_atTop_add_const_left _ T₀ (tendsto_natCast_atTop_atTop.atTop_mul_const hY)
    have hbot : Tendsto (fun N : ℕ => -(T₀ + (N : ℝ) * Y)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp htop
    have hlim := intervalIntegral_tendsto_integral hint hbot htop
    refine le_of_tendsto' hlim fun N => ?_
    show ∫ t in (-(T₀ + N * Y))..(T₀ + N * Y), (1 + H * |t| / Y) ^ (-(j : ℝ)) * g t ≤ _
    have hsplit : ∫ t in (-(T₀ + N * Y))..(T₀ + N * Y), (1 + H * |t| / Y) ^ (-(j : ℝ)) * g t =
        (∫ t in (-(T₀ + N * Y))..(-T₀), (1 + H * |t| / Y) ^ (-(j : ℝ)) * g t) +
          (∫ t in (-T₀)..T₀, (1 + H * |t| / Y) ^ (-(j : ℝ)) * g t) +
          ∫ t in T₀..(T₀ + N * Y), (1 + H * |t| / Y) ^ (-(j : ℝ)) * g t := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _)
        (hfc.intervalIntegrable _ _), intervalIntegral.integral_add_adjacent_intervals
        (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _)]
    have hmid : ∫ t in (-T₀)..T₀, (1 + H * |t| / Y) ^ (-(j : ℝ)) * g t ≤
        ∫ t in (-T₀)..T₀, g t :=
      intervalIntegral.integral_mono_on (by linarith) (hfc.intervalIntegrable _ _)
        (hg.intervalIntegrable _ _) fun t _ => by
          have h := mul_le_mul_of_nonneg_right (hW1 t) (hg0 t)
          rwa [one_mul] at h
    rw [hsplit]
    have h1 := (hneg N).trans (hsumω N)
    have h2 := (hpos N).trans (hsumω N)
    linarith
  · rw [integral_undef hint]
    have h1 : 0 ≤ ∫ t in (-T₀)..T₀, g t :=
      intervalIntegral.integral_nonneg (by linarith) fun t _ => hg0 t
    have h2 : 0 ≤ 2 * G * (Λ ^ (j - 1))⁻¹ :=
      mul_nonneg (mul_nonneg zero_le_two hG0) (inv_nonneg.mpr (pow_nonneg hΛ.le _))
    linarith

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
