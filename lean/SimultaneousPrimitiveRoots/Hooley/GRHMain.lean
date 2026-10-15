module

public import SimultaneousPrimitiveRoots.Hooley.ExceptionRanges
public import SimultaneousPrimitiveRoots.AsymptoticAssembly

/-!
# The simultaneous primitive-root bound from GRH-strength splitting estimates

Hooley's method, run on the fixed residue classes chosen from the square condition, proves
`MainClaim` from the splitting estimate `GRHSplittingBound` alone.

The candidate supply is unconditional: it is the prime number theorem in a fixed residue
class, proved in `Hooley.ResiduePrimes` from the Chebotarev density theorem of Tau Ceti.
In particular no candidate-supply hypothesis (no long prime factor of `p - 1`) and no
zero-free strip of fixed width are assumed. The only analytic input is `GRHSplittingBound`,
a classical consequence of the generalized Riemann hypothesis for Kummer fields.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Filter Asymptotics Finset
open scoped Topology
noncomputable section
open Classical

/-- `log⁴ x ≤ x^(1/4) / 2` for large `x`. -/
theorem eventually_log_pow_four_le :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ 4 ≤ x ^ (1 / 4 : ℝ) / 2 := by
  have h := (isLittleO_log_rpow_rpow_atTop (4 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4)).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hx0 : 0 < x := by linarith
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
  have h4 : Real.log x ^ (4 : ℝ) = Real.log x ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h4] at hx
  linarith

theorem sqrt_eq_rpow_quarter_mul {x : ℝ} (hx : 0 < x) :
    Real.sqrt x = x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) := by
  rw [← Real.rpow_add hx, Real.sqrt_eq_rpow]
  norm_num

/-- For large `x`, the GRH cutoff is at least `x^(1/4)` and at least half of `√x / log⁴ x`. -/
theorem eventually_grhCutoff_bounds :
    ∀ᶠ x : ℝ in atTop, x ^ (1 / 4 : ℝ) ≤ (grhCutoff x : ℝ) ∧
      Real.sqrt x / Real.log x ^ 4 ≤ 2 * (grhCutoff x : ℝ) := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop (2 : ℝ)
  filter_upwards [eventually_log_pow_four_le, ht, eventually_gt_atTop (1 : ℝ)] with
    x hlog ht2 hx1
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hL4 : 0 < Real.log x ^ 4 := by positivity
  set t := x ^ (1 / 4 : ℝ) with htdef
  have hsqrt : Real.sqrt x = t * t := sqrt_eq_rpow_quarter_mul hx0
  have hbig : 2 * t ≤ Real.sqrt x / Real.log x ^ 4 := by
    rw [le_div_iff₀ hL4, hsqrt]
    nlinarith
  have hfl := Nat.lt_floor_add_one (Real.sqrt x / Real.log x ^ 4)
  change Real.sqrt x / Real.log x ^ 4 < (grhCutoff x : ℝ) + 1 at hfl
  constructor
  · linarith
  · linarith

/-- `1 ≤ log x` once `x ≥ e`. -/
theorem one_le_log_of_exp_one_le {x : ℝ} (hx : Real.exp 1 ≤ x) : 1 ≤ Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  exact (Real.le_log_iff_exp_le hx0).mpr hx

/-- **The window of prime reciprocals tends to zero.** -/
theorem exists_window_reciprocal_bound : ∃ w : ℝ → ℝ, Tendsto w atTop (𝓝 0) ∧
    ∀ᶠ x : ℝ in atTop,
      ∑ q ∈ (Ioc (grhCutoff x) (orderCutoff x)).filter Nat.Prime, (1 / (q : ℝ)) ≤ w x := by
  obtain ⟨C, hC, N, hπ⟩ := exists_chebyshev_constant
  refine ⟨fun x => 8 * C * (2 / Real.log x +
    6 / Real.log 2 * (Real.log (Real.log x) / Real.log x)), ?_, ?_⟩
  · have h1 : Tendsto (fun x : ℝ => 2 / Real.log x) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds Real.tendsto_log_atTop
    have h2 : Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (𝓝 0) := by
      have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        Real.tendsto_log_atTop
      apply h.congr
      intro x
      simp
    have h3 := (h1.add (h2.const_mul (6 / Real.log 2))).const_mul (8 * C)
    simpa using h3
  · have hbig := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop
      ((max N 2 : ℕ) : ℝ)
    filter_upwards [eventually_grhCutoff_bounds, hbig, eventually_ge_atTop (Real.exp 1)] with
      x hX0 hxbig hxe
    obtain ⟨hX0a, hX0b⟩ := hX0
    have hL1 : 1 ≤ Real.log x := one_le_log_of_exp_one_le hxe
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
    have hL : 0 < Real.log x := by linarith
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    set X0 := grhCutoff x with hX0def
    set X1 := orderCutoff x with hX1def
    have hX0N : max N 2 ≤ X0 := by exact_mod_cast hxbig.trans hX0a
    have hwin := prime_reciprocal_window_le hC hπ (a := X0) (b := X1)
      ((le_max_left N 2).trans hX0N) ((le_max_right N 2).trans hX0N)
    have hX0pos : (0 : ℝ) < X0 := by
      have : (2 : ℝ) ≤ X0 := by exact_mod_cast (le_max_right N 2).trans hX0N
      linarith
    -- `log X0 ≥ log x / 4`
    have hlogX0 : Real.log x / 4 ≤ Real.log X0 := by
      have h := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hX0a
      rw [Real.log_rpow hx0] at h
      linarith
    -- `log₂ (X1 / X0) ≤ (log 2 + 6 log log x) / log 2`
    have hloglog : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL1
    have hnatlog : (Nat.log 2 (X1 / X0) : ℝ) ≤
        (Real.log 2 + 6 * Real.log (Real.log x)) / Real.log 2 := by
      by_cases hq : X1 / X0 = 0
      · rw [hq, Nat.log_zero_right, Nat.cast_zero]
        positivity
      · refine (natLog_two_le_log_div hq).trans ?_
        apply div_le_div_of_nonneg_right _ hl2.le
        have hqpos : (0 : ℝ) < ((X1 / X0 : ℕ) : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hq
        have hX1le : (X1 : ℝ) ≤ Real.sqrt x * Real.log x ^ 2 :=
          Nat.floor_le (by positivity)
        have hratio : ((X1 / X0 : ℕ) : ℝ) ≤ 2 * Real.log x ^ 6 := by
          calc ((X1 / X0 : ℕ) : ℝ) ≤ (X1 : ℝ) / X0 := Nat.cast_div_le
            _ ≤ 2 * Real.log x ^ 6 := by
              rw [div_le_iff₀ hX0pos]
              have hL4 : 0 < Real.log x ^ 4 := by positivity
              have hs : Real.sqrt x ≤ 2 * (X0 : ℝ) * Real.log x ^ 4 := by
                have := (div_le_iff₀ hL4).mp hX0b
                linarith
              have hL2 : 0 ≤ Real.log x ^ 2 := by positivity
              calc (X1 : ℝ) ≤ Real.sqrt x * Real.log x ^ 2 := hX1le
                _ ≤ (2 * (X0 : ℝ) * Real.log x ^ 4) * Real.log x ^ 2 :=
                    mul_le_mul_of_nonneg_right hs hL2
                _ = 2 * Real.log x ^ 6 * X0 := by ring
        calc Real.log ((X1 / X0 : ℕ) : ℝ) ≤ Real.log (2 * Real.log x ^ 6) :=
              Real.log_le_log hqpos hratio
          _ = Real.log 2 + 6 * Real.log (Real.log x) := by
              rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
              push_cast
              ring
    have hfac : 0 ≤ (Nat.log 2 (X1 / X0) : ℝ) + 1 := by positivity
    calc ∑ q ∈ (Ioc X0 X1).filter Nat.Prime, (1 / (q : ℝ))
        ≤ 2 * C / Real.log X0 * ((Nat.log 2 (X1 / X0) : ℝ) + 1) := hwin
      _ ≤ 2 * C / (Real.log x / 4) * ((Nat.log 2 (X1 / X0) : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_right _ hfac
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hlogX0
      _ ≤ 2 * C / (Real.log x / 4) *
            ((Real.log 2 + 6 * Real.log (Real.log x)) / Real.log 2 + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = 8 * C * (2 / Real.log x +
            6 / Real.log 2 * (Real.log (Real.log x) / Real.log x)) := by
          field_simp
          ring

/-- `√x · x^(1/8) = x / x^(3/8)`. -/
theorem sqrt_mul_rpow_eighth {x : ℝ} (hx : 0 < x) :
    Real.sqrt x * x ^ (1 / 8 : ℝ) = x / x ^ (3 / 8 : ℝ) := by
  have h1 : Real.sqrt x * x ^ (1 / 8 : ℝ) = x ^ (5 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    norm_num
  have h2 : x / x ^ (3 / 8 : ℝ) = x ^ (5 / 8 : ℝ) := by
    rw [show (5 / 8 : ℝ) = 1 - 3 / 8 by norm_num, Real.rpow_sub hx, Real.rpow_one]
  rw [h1, h2]

/-- **Total error of the three ranges.** Beyond the main term `|A| C / Y`, the exceptions are
`o(x / log x)` uniformly in `Y`. -/
theorem exists_exception_error (A : Finset ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∃ ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ Y : ℕ, 1 ≤ Y → (∀ a ∈ A, a ≤ Y) → (∀ a ∈ A, 2 ≤ a) →
        (∀ a ∈ A, GRHSplittingBoundUpTo a C) →
        ∀ᶠ x : ℝ in atTop,
          ((smallOrderAt A x).card : ℝ) + (grhRangeExceptions A Y x).card +
              (windowExceptions x).card ≤
            (x / Real.log x) * ((A.card : ℝ) * C / Y + ε x) := by
  obtain ⟨w, hw, hwbound⟩ := exists_window_reciprocal_bound
  set SA : ℝ := ∑ a ∈ A, Real.log a with hSA
  refine ⟨fun x => 4 * SA / Real.log x ^ 4 + (A.card : ℝ) * (9 / 4 * C) / Real.log x +
    96 * w x + 32 * (Real.log x ^ 6 / x ^ (3 / 8 : ℝ)), ?_, ?_⟩
  · have hL4 : Tendsto (fun x : ℝ => Real.log x ^ 4) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop
    have t1 : Tendsto (fun x : ℝ => 4 * SA / Real.log x ^ 4) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hL4
    have t2 : Tendsto (fun x : ℝ => (A.card : ℝ) * (9 / 4 * C) / Real.log x) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds Real.tendsto_log_atTop
    have t3 : Tendsto (fun x : ℝ => 96 * w x) atTop (𝓝 0) := by
      simpa using hw.const_mul 96
    have t4 : Tendsto (fun x : ℝ => 32 * (Real.log x ^ 6 / x ^ (3 / 8 : ℝ))) atTop (𝓝 0) := by
      have h := (isLittleO_log_rpow_rpow_atTop (6 : ℝ)
        (by norm_num : (0 : ℝ) < 3 / 8)).tendsto_div_nhds_zero
      have h' : Tendsto (fun x : ℝ => Real.log x ^ 6 / x ^ (3 / 8 : ℝ)) atTop (𝓝 0) := by
        apply h.congr
        intro x
        rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      simpa using h'.const_mul 32
    simpa using ((t1.add t2).add t3).add t4
  · intro Y hY hYbase hpos hGRH
    have hall : ∀ᶠ x : ℝ in atTop, ∀ a ∈ A, ∀ q : ℕ, q.Prime → a < q → q ≤ grhCutoff x →
        ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
          C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
            C * Real.sqrt x * Real.log ((q : ℝ) * x) ^ 2 :=
      (Filter.eventually_all_finset A).mpr hGRH
    filter_upwards [hwbound, eventually_grhCutoff_bounds, eventually_ge_atTop (Real.exp 1),
      eventually_ge_atTop (3 : ℝ), hall] with x hxw hX0 hxe hx3 hGRHx
    obtain ⟨hX0a, _⟩ := hX0
    have hL1 : 1 ≤ Real.log x := one_le_log_of_exp_one_le hxe
    have hx0 : 0 < x := by linarith
    have hx1 : 1 < x := by linarith
    have hL : 0 < Real.log x := by linarith
    have hscale : 0 < x / Real.log x := div_pos hx0 hL
    have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hsqsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have hSA : 0 ≤ SA := by
      apply sum_nonneg
      intro a ha
      exact Real.log_nonneg (by exact_mod_cast (by have := hpos a ha; omega : 1 ≤ a))
    -- (i) small orders
    have hm : (smallOrderCutoff x : ℝ) ≤ 2 * Real.sqrt x / Real.log x ^ 2 :=
      Nat.floor_le (by positivity)
    have hm0 : (0 : ℝ) ≤ smallOrderCutoff x := Nat.cast_nonneg _
    have hm2 : (smallOrderCutoff x : ℝ) ^ 2 ≤ 4 * x / Real.log x ^ 4 := by
      have h := pow_le_pow_left₀ hm0 hm 2
      calc (smallOrderCutoff x : ℝ) ^ 2 ≤ (2 * Real.sqrt x / Real.log x ^ 2) ^ 2 := h
        _ = 4 * x / Real.log x ^ 4 := by
            rw [div_pow, mul_pow, sq (Real.sqrt x), hsqsq]
            ring
    have hsmall : ((smallOrderAt A x).card : ℝ) ≤
        (x / Real.log x) * (4 * SA / Real.log x ^ 4) := by
      calc ((smallOrderAt A x).card : ℝ) ≤ SA * (smallOrderCutoff x : ℝ) ^ 2 / Real.log x :=
            smallOrderAt_card_le hpos hx1
        _ ≤ SA * (4 * x / Real.log x ^ 4) / Real.log x := by
            apply div_le_div_of_nonneg_right _ hL.le
            exact mul_le_mul_of_nonneg_left hm2 hSA
        _ = (x / Real.log x) * (4 * SA / Real.log x ^ 4) := by
            field_simp
    -- (ii) GRH range
    have hgrh := grhRangeExceptions_card_le hY hYbase hC hx3 hGRHx
    have hX0le : (grhCutoff x : ℝ) ≤ Real.sqrt x / Real.log x ^ 4 :=
      Nat.floor_le (by positivity)
    have hX0one : (1 : ℝ) ≤ grhCutoff x :=
      le_trans (Real.one_le_rpow hx1.le (by norm_num)) hX0a
    have hX0sqrt : (grhCutoff x : ℝ) ≤ Real.sqrt x := by
      refine hX0le.trans ?_
      apply div_le_self hsqrt0
      exact one_le_pow₀ hL1
    have hlogX0x : Real.log ((grhCutoff x : ℝ) * x) ≤ 3 / 2 * Real.log x := by
      calc Real.log ((grhCutoff x : ℝ) * x) ≤ Real.log (Real.sqrt x * x) :=
            Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hX0sqrt hx0.le)
        _ = 3 / 2 * Real.log x := by
            rw [Real.log_mul (by positivity) hx0.ne', Real.log_sqrt hx0.le]
            ring
    have hlogX0x0 : 0 ≤ Real.log ((grhCutoff x : ℝ) * x) := Real.log_nonneg (by nlinarith)
    have hlogsq : Real.log ((grhCutoff x : ℝ) * x) ^ 2 ≤ 9 / 4 * Real.log x ^ 2 := by
      have h := pow_le_pow_left₀ hlogX0x0 hlogX0x 2
      calc Real.log ((grhCutoff x : ℝ) * x) ^ 2 ≤ (3 / 2 * Real.log x) ^ 2 := h
        _ = 9 / 4 * Real.log x ^ 2 := by ring
    have herr2 : C * (grhCutoff x : ℝ) * (Real.sqrt x * Real.log ((grhCutoff x : ℝ) * x) ^ 2) ≤
        (x / Real.log x) * (9 / 4 * C / Real.log x) := by
      have hL4 : 0 < Real.log x ^ 4 := by positivity
      calc C * (grhCutoff x : ℝ) * (Real.sqrt x * Real.log ((grhCutoff x : ℝ) * x) ^ 2)
          ≤ C * (Real.sqrt x / Real.log x ^ 4) * (Real.sqrt x * (9 / 4 * Real.log x ^ 2)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hX0le hC)
              (mul_le_mul_of_nonneg_left hlogsq hsqrt0) (by positivity) (by positivity)
        _ = (x / Real.log x) * (9 / 4 * C / Real.log x) := by
            rw [show C * (Real.sqrt x / Real.log x ^ 4) * (Real.sqrt x * (9 / 4 * Real.log x ^ 2))
              = C * (Real.sqrt x * Real.sqrt x) * (9 / 4) / Real.log x ^ 2 by
                field_simp]
            rw [hsqsq]
            field_simp
    -- (iii) window
    have hwin := windowExceptions_card_le hx1
    have hlogy : Real.log (x ^ (1 / 8 : ℝ)) = Real.log x / 8 := by
      rw [Real.log_rpow hx0]
      ring
    have hN : ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * x := by
      push_cast
      have := Nat.floor_le (show (0 : ℝ) ≤ 2 * x by linarith)
      linarith
    have hfirst : 4 * ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ) / Real.log (x ^ (1 / 8 : ℝ)) ≤
        (x / Real.log x) * 96 := by
      rw [hlogy]
      rw [div_le_iff₀ (by positivity)]
      have : (x / Real.log x) * 96 * (Real.log x / 8) = 12 * x := by
        field_simp
        ring
      rw [this]
      linarith
    have hwsum0 : 0 ≤ ∑ q ∈ (Ioc (grhCutoff x) (orderCutoff x)).filter Nat.Prime,
        (1 / (q : ℝ)) := sum_nonneg fun q _ => by positivity
    have hy1 : 1 ≤ x ^ (1 / 8 : ℝ) := Real.one_le_rpow hx1.le (by norm_num)
    have hE : x ^ (1 / 8 : ℝ) * (1 + Real.log (x ^ (1 / 8 : ℝ))) ^ 3 + x ^ (1 / 8 : ℝ) + 2 ≤
        32 * x ^ (1 / 8 : ℝ) * Real.log x ^ 3 := by
      rw [hlogy]
      have h1 : 1 + Real.log x / 8 ≤ 2 * Real.log x := by linarith
      have h1' : (1 + Real.log x / 8) ^ 3 ≤ (2 * Real.log x) ^ 3 :=
        pow_le_pow_left₀ (by positivity) h1 3
      have hL3 : 1 ≤ Real.log x ^ 3 := one_le_pow₀ hL1
      nlinarith
    have hX1 : (orderCutoff x : ℝ) ≤ Real.sqrt x * Real.log x ^ 2 :=
      Nat.floor_le (by positivity)
    have hsecond : (orderCutoff x : ℝ) *
        (x ^ (1 / 8 : ℝ) * (1 + Real.log (x ^ (1 / 8 : ℝ))) ^ 3 + x ^ (1 / 8 : ℝ) + 2) ≤
          (x / Real.log x) * (32 * (Real.log x ^ 6 / x ^ (3 / 8 : ℝ))) := by
      have hE0 : 0 ≤ x ^ (1 / 8 : ℝ) * (1 + Real.log (x ^ (1 / 8 : ℝ))) ^ 3 +
          x ^ (1 / 8 : ℝ) + 2 := by
        have hc : 0 ≤ (1 + Real.log (x ^ (1 / 8 : ℝ))) ^ 3 :=
          pow_nonneg (by rw [hlogy]; linarith) 3
        have hr : 0 ≤ x ^ (1 / 8 : ℝ) := Real.rpow_nonneg hx0.le _
        exact add_nonneg (add_nonneg (mul_nonneg hr hc) hr) (by norm_num)
      calc (orderCutoff x : ℝ) *
            (x ^ (1 / 8 : ℝ) * (1 + Real.log (x ^ (1 / 8 : ℝ))) ^ 3 + x ^ (1 / 8 : ℝ) + 2)
          ≤ (Real.sqrt x * Real.log x ^ 2) * (32 * x ^ (1 / 8 : ℝ) * Real.log x ^ 3) :=
            mul_le_mul hX1 hE hE0 (by positivity)
        _ = 32 * (Real.sqrt x * x ^ (1 / 8 : ℝ)) * Real.log x ^ 5 := by ring
        _ = 32 * (x / x ^ (3 / 8 : ℝ)) * Real.log x ^ 5 := by rw [sqrt_mul_rpow_eighth hx0]
        _ = (x / Real.log x) * (32 * (Real.log x ^ 6 / x ^ (3 / 8 : ℝ))) := by
            have hr : 0 < x ^ (3 / 8 : ℝ) := Real.rpow_pos_of_pos hx0 _
            field_simp
    have hwindow : ((windowExceptions x).card : ℝ) ≤
        (x / Real.log x) * (96 * w x) +
          (x / Real.log x) * (32 * (Real.log x ^ 6 / x ^ (3 / 8 : ℝ))) := by
      have h1 : 4 * ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ) / Real.log (x ^ (1 / 8 : ℝ)) *
          (∑ q ∈ (Ioc (grhCutoff x) (orderCutoff x)).filter Nat.Prime, (1 / (q : ℝ))) ≤
            (x / Real.log x) * 96 * w x := by
        apply mul_le_mul hfirst hxw hwsum0 (by positivity)
      linarith
    -- total
    have htotal_grh : ((grhRangeExceptions A Y x).card : ℝ) ≤
        (A.card : ℝ) * C / Y * (x / Real.log x) +
          (x / Real.log x) * ((A.card : ℝ) * (9 / 4 * C) / Real.log x) := by
      have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
      calc ((grhRangeExceptions A Y x).card : ℝ) ≤ (A.card : ℝ) * (C / Y * (x / Real.log x) +
            C * (grhCutoff x : ℝ) * (Real.sqrt x * Real.log ((grhCutoff x : ℝ) * x) ^ 2)) := hgrh
        _ ≤ (A.card : ℝ) * (C / Y * (x / Real.log x) +
            (x / Real.log x) * (9 / 4 * C / Real.log x)) := by
            apply mul_le_mul_of_nonneg_left _ hA0
            linarith
        _ = (A.card : ℝ) * C / Y * (x / Real.log x) +
            (x / Real.log x) * ((A.card : ℝ) * (9 / 4 * C) / Real.log x) := by ring
    have hgoal : (x / Real.log x) * ((A.card : ℝ) * C / Y +
        (4 * SA / Real.log x ^ 4 + (A.card : ℝ) * (9 / 4 * C) / Real.log x + 96 * w x +
          32 * (Real.log x ^ 6 / x ^ (3 / 8 : ℝ)))) =
        (x / Real.log x) * (4 * SA / Real.log x ^ 4) +
          ((A.card : ℝ) * C / Y * (x / Real.log x) +
            (x / Real.log x) * ((A.card : ℝ) * (9 / 4 * C) / Real.log x)) +
          ((x / Real.log x) * (96 * w x) +
            (x / Real.log x) * (32 * (Real.log x ^ 6 / x ^ (3 / 8 : ℝ)))) := by ring
    show _ ≤ (x / Real.log x) * ((A.card : ℝ) * C / Y +
        (4 * SA / Real.log x ^ 4 + (A.card : ℝ) * (9 / 4 * C) / Real.log x + 96 * w x +
          32 * (Real.log x ^ 6 / x ^ (3 / 8 : ℝ))))
    rw [hgoal]
    linarith

/-- **Simultaneous primitive roots from GRH-strength splitting (Hooley's method).**
For an admissible `A`, the GRH-strength splitting estimates for the bases of `A` imply the
positive dyadic lower bound. The candidate supply is the unconditional prime number theorem
in fixed residue classes. -/
theorem positiveDyadicLowerBound_of_grhSplittingUpTo {A : Finset ℕ} (hA : Admissible A)
    {C : ℝ} (hC : 0 ≤ C) (hGRH : ∀ a ∈ A, GRHSplittingBoundUpTo a C) :
    PositiveDyadicLowerBound A := by
  classical
  obtain ⟨M, hM, hselector⟩ := exists_selector_with_progressionConditions hA.2.1 hA.2.2
  have hphi : 0 < (Nat.totient M : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hM
  set K : ℝ := (A.card : ℝ) * C with hKdef
  have hK0 : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) hC
  set θ : ℝ := 1 / 2 with hθdef
  have hθ : 0 < θ := by norm_num
  obtain ⟨T, hTlarge⟩ := exists_nat_gt
    (max 1 (max (4 * K * (Nat.totient M : ℝ) / θ) ((A.sup id : ℕ) : ℝ)))
  have hTreal : 1 < (T : ℝ) := (le_max_left _ _).trans_lt hTlarge
  have hT : 1 ≤ T := by exact_mod_cast hTreal.le
  have hTpos : 0 < (T : ℝ) := by linarith
  have hlarge : 4 * K * (Nat.totient M : ℝ) ≤ θ * (T : ℝ) := by
    have hd : 4 * K * (Nat.totient M : ℝ) / θ < (T : ℝ) :=
      (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hTlarge)
    have := (div_lt_iff₀ hθ).mp hd
    nlinarith
  have hbase_cutoff : ∀ a ∈ A, a ≤ 2 * T ^ 2 + 1 := by
    intro a ha
    have hsup : ((A.sup id : ℕ) : ℝ) < (T : ℝ) :=
      (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hTlarge)
    have hnat : A.sup id < T := by exact_mod_cast hsup
    have haT : a < T := (Finset.le_sup (f := id) ha).trans_lt hnat
    have hTpow : T ≤ T ^ 2 := Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) T
    omega
  obtain ⟨H, R, hH, _, hdensity, hregular, hprogressions⟩ := hselector T hT
  have hgap : K / (2 * (T : ℝ) ^ 2 + 1) < θ / (2 * (Nat.totient M : ℝ) * (T : ℝ)) :=
    positive_parameter_difference hθ hphi hTpos hlarge
  set g : ℝ := θ / (2 * (Nat.totient M : ℝ) * (T : ℝ)) - K / (2 * (T : ℝ) ^ 2 + 1) with hgdef
  have hg : 0 < g := sub_pos.mpr hgap
  obtain ⟨ε, hε, hexc⟩ := exists_exception_error A hC
  have hexc' := hexc (2 * T ^ 2 + 1) (by omega) hbase_cutoff hA.2.1 hGRH
  have hsup := progressionCandidates_supply hH hregular (θ := θ) (by norm_num)
  have hεsmall := hε.eventually (gt_mem_nhds (half_pos hg))
  apply positiveDyadicLowerBound_of_eventually (half_pos hg)
  filter_upwards [hsup, hexc', hεsmall, eventually_ge_atTop (3 : ℝ)] with x hxs hxe hxε hx3
  have hscale : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos (by linarith))
  have hcap := candidates_sub_bad_le_primeCount (A := A) (C := progressionCandidates H R x)
    (fun p hp => ⟨(Finset.mem_filter.mp hp).2.2.1, (Finset.mem_filter.mp hp).2.2.2.1⟩)
  have hbad : ((badCandidates A (progressionCandidates H R x)).card : ℝ) ≤
      ((smallOrderAt A x).card : ℝ) + (grhRangeExceptions A (2 * T ^ 2 + 1) x).card +
        (windowExceptions x).card := by
    have hsub := bad_progressionCandidates_subset hA.2.1 hx3 hprogressions
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (smallOrderAt A x ∪ grhRangeExceptions A (2 * T ^ 2 + 1) x)
      (windowExceptions x)
    have h3 := Finset.card_union_le (smallOrderAt A x) (grhRangeExceptions A (2 * T ^ 2 + 1) x)
    have hnat : (badCandidates A (progressionCandidates H R x)).card ≤
        (smallOrderAt A x).card + (grhRangeExceptions A (2 * T ^ 2 + 1) x).card +
          (windowExceptions x).card := by omega
    exact_mod_cast hnat
  have hlower : θ / (2 * (Nat.totient M : ℝ) * (T : ℝ)) * (x / Real.log x) ≤
      ((progressionCandidates H R x).card : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdensity hθ.le) hscale.le
    have heq : θ * (1 / (2 * (Nat.totient M : ℝ) * (T : ℝ))) =
        θ / (2 * (Nat.totient M : ℝ) * (T : ℝ)) := by ring
    rw [heq] at hmul
    exact hmul.trans hxs
  have hYcast : (((2 * T ^ 2 + 1 : ℕ) : ℕ) : ℝ) = 2 * (T : ℝ) ^ 2 + 1 := by push_cast; ring
  rw [hYcast] at hxe
  have hεle : (x / Real.log x) * ε x ≤ (x / Real.log x) * (g / 2) :=
    mul_le_mul_of_nonneg_left hxε.le hscale.le
  have hexpand : (x / Real.log x) * ((A.card : ℝ) * C / (2 * (T : ℝ) ^ 2 + 1) + ε x) =
      K / (2 * (T : ℝ) ^ 2 + 1) * (x / Real.log x) + (x / Real.log x) * ε x := by
    rw [hKdef]
    ring
  have hfinal : g / 2 * (x / Real.log x) =
      θ / (2 * (Nat.totient M : ℝ) * (T : ℝ)) * (x / Real.log x) -
        K / (2 * (T : ℝ) ^ 2 + 1) * (x / Real.log x) - (x / Real.log x) * (g / 2) := by
    rw [hgdef]
    ring
  rw [hexpand] at hxe
  linarith

/-- The same bound from the global form of the splitting estimate. -/
theorem positiveDyadicLowerBound_of_grhSplitting {A : Finset ℕ} (hA : Admissible A)
    {C : ℝ} (hC : 0 ≤ C) (hGRH : ∀ a ∈ A, GRHSplittingBound a C) :
    PositiveDyadicLowerBound A :=
  positiveDyadicLowerBound_of_grhSplittingUpTo hA hC fun a ha => (hGRH a ha).upTo

/-- **`MainClaim` from GRH-strength splitting estimates in Hooley's range.** If every base
`a ≥ 2` satisfies the splitting estimate for large `x` and `q ≤ √x / log⁴ x` (a consequence of
GRH for the Kummer fields `ℚ(ζ_q, a^(1/q))`), then every admissible set has a positive dyadic
lower bound. No candidate-supply hypothesis is assumed. -/
theorem mainClaim_of_grhSplittingUpTo
    (hGRH : ∀ a : ℕ, 2 ≤ a → ∃ C : ℝ, 0 ≤ C ∧ GRHSplittingBoundUpTo a C) : MainClaim := by
  intro A hA
  choose! c hc0 hc using hGRH
  refine positiveDyadicLowerBound_of_grhSplittingUpTo hA (C := ∑ a ∈ A, c a)
    (sum_nonneg fun a ha => hc0 a (hA.2.1 a ha)) ?_
  intro a ha
  apply (hc a (hA.2.1 a ha)).mono
  exact single_le_sum (fun b hb => hc0 b (hA.2.1 b hb)) ha

/-- **`MainClaim` from GRH-strength splitting estimates.** -/
theorem mainClaim_of_grhSplitting
    (hGRH : ∀ a : ℕ, 2 ≤ a → ∃ C : ℝ, 0 ≤ C ∧ GRHSplittingBound a C) : MainClaim := by
  apply mainClaim_of_grhSplittingUpTo
  intro a ha
  obtain ⟨C, hC, h⟩ := hGRH a ha
  exact ⟨C, hC, h.upTo⟩

end
end SimultaneousPrimitiveRoots
