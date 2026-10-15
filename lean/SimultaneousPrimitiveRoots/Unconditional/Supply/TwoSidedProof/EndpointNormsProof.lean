module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.ListNorm

/-!
# The endpoint norms (cor:list-norm)

`endpointNormsLink d : EndpointNormsLink d` (`[P-06:0262–0285]`), for every number of slots: from
the boundedness of `F_x` on power ranges (`CorePowerBounded d`) and the divisor moments, both
endpoint vectors have squared norm at most `X L^{2C₃}` on every enlarged dyad `[X, 4X)`,
`x^{1/2} ≤ X ≤ x²`, with an exponent `C₃` that does not depend on the number `J` of first slots.

By `sum_mul_dampedMass_le` (`TwoSidedProof/ListNorm.lean`) it suffices to bound, for every product
`m` of active primes, the sum of the squares of the endpoint over the multiples of `m` in the
dyad by `R / m`; these multiples are the `m v` with `1 ≤ v ≤ 4X/m` (`sum_wideWindow_dvd_le`).

* First endpoint: `|F_x(m v)| ≤ B` (`CorePowerBounded d` with `κ = 3`, since `m v < 4X ≤ x³`), so
  the sum is at most `B² · 4X/m`.
* Second endpoint: `|G(m v)| ≤ L^C τ(v)^k`, `k = ⌈C⌉₊` (`norm_core_mul_le`: `(m v)_* ∣ v`), and the
  divisor moment of order `2k` on `v ≤ 8X/m` (the range is doubled so that `log(16X/m) ≥ 1`) with
  `log(16X/m) ≤ 3L`.

The exponent is `C₃ = max(1, 2C + max(A, 0) + 1)/2` with `A` the exponent of the divisor moment of
order `2⌈C⌉₊`; it depends on the fixed data only through the growth exponent `C` of the second
endpoint.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open Filter
open scoped Topology

/-- **The endpoint norms** (`[P-06:0262–0285]`, (cor:list-norm)) from the boundedness of `F_x` on
power ranges and the divisor moments, for every number of slots. This is the field
`endpointNorms` of `OpenLeaves d H 𝔅`. -/
theorem endpointNormsLink (d : ℕ) : EndpointNormsLink d := by
  intro hCP D
  obtain ⟨B, -, hB⟩ := hCP D.q D.q_pos D.q_lt_one D.ε D.ε_pos 3 (by norm_num) D.K
  obtain ⟨xc, hc⟩ := hB D.𝔞
  obtain ⟨Cd, Ad, hCd, hdiv⟩ := (divisorMoments (⌈D.C⌉₊ * 2)).1
  refine ⟨max 1 (D.C * 2 + max Ad 0 + 1) / 2, fun J => ?_⟩
  have h1 : ∀ᶠ x : ℝ in atTop,
      max (max (4 * B ^ 2) (Cd * 8 * (3 : ℝ) ^ max Ad 0)) 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp
    ((h1.and (eventually_ge_atTop xc)).and (eventually_ge_atTop (16 : ℝ)))
  unfold EndpointNormsAt
  refine ⟨x₀, fun x hx I X hXlo hXhi => ?_⟩
  obtain ⟨⟨hL, hxc⟩, hx16⟩ := hx₀ x hx
  -- the size conditions
  have hL1 : 1 ≤ Real.log x := (le_max_right _ _).trans hL
  have hLB : 4 * B ^ 2 ≤ Real.log x := ((le_max_left _ _).trans (le_max_left _ _)).trans hL
  have hLD : Cd * 8 * (3 : ℝ) ^ max Ad 0 ≤ Real.log x :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have hX1 : 1 ≤ X := (Real.one_le_rpow hx1 (by norm_num)).trans hXlo
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX1
  have hX2 : X ≤ x ^ 2 := by
    rw [Real.rpow_two] at hXhi
    exact hXhi
  have h16X : 16 * X ≤ x ^ 3 :=
    calc 16 * X ≤ x * x ^ 2 := mul_le_mul hx16 hX2 hX0.le hx0.le
      _ = x ^ 3 := by ring
  have hx3 : x ^ (3 : ℝ) = x ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast x 3
  have h4X : 4 * X ≤ x ^ (3 : ℝ) := by
    rw [hx3]
    linarith
  -- powers of `L`
  have hrp : ∀ a : ℝ, 0 ≤ Real.log x ^ a := fun a => Real.rpow_nonneg hL0.le a
  have h2C₃ : 2 * (max 1 (D.C * 2 + max Ad 0 + 1) / 2) = max 1 (D.C * 2 + max Ad 0 + 1) := by
    ring
  have hmaxF : Real.log x ≤ Real.log x ^ (2 * (max 1 (D.C * 2 + max Ad 0 + 1) / 2)) := by
    rw [h2C₃]
    calc Real.log x = Real.log x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Real.log x ^ max 1 (D.C * 2 + max Ad 0 + 1) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)
  have hmaxG : Real.log x ^ (D.C * 2 + max Ad 0 + 1) ≤
      Real.log x ^ (2 * (max 1 (D.C * 2 + max Ad 0 + 1) / 2)) := by
    rw [h2C₃]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right _ _)
  have hEG : Real.log x ^ (D.C * 2 + max Ad 0 + 1) =
      Real.log x ^ (D.C * 2) * Real.log x ^ max Ad 0 * Real.log x := by
    rw [Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_one]
  have hsq : (Real.log x ^ D.C) ^ 2 = Real.log x ^ (D.C * 2) := by
    rw [Real.rpow_mul hL0.le, Real.rpow_two]
  constructor
  · -- the first endpoint
    refine (sum_mul_dampedMass_le I.groups J D.q₀_pos D.q₀_lt_one (wideWindow X)
      (fun n : ℤ => centeredCore D.q D.𝔞 x I.S n.toNat ^ 2) (fun n => sq_nonneg _)
      (R := 4 * X * B ^ 2) ?_).trans ?_
    · intro m hm _
      have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
      have h4Xm : 0 ≤ 4 * X / (m : ℝ) := div_nonneg (by linarith) hmR.le
      refine (sum_wideWindow_dvd_le
        (a := fun n : ℤ => centeredCore D.q D.𝔞 x I.S n.toNat ^ 2)
        (fun n => sq_nonneg _) hX1 hm).trans ?_
      have hterm : ∀ v ∈ Finset.Icc 1 ⌊4 * X / (m : ℝ)⌋₊,
          centeredCore D.q D.𝔞 x I.S ((m * v : ℕ) : ℤ).toNat ^ 2 ≤ B ^ 2 := by
        intro v hv
        obtain ⟨hv1, hv2⟩ := Finset.mem_Icc.mp hv
        have hmv1 : 1 ≤ m * v := Nat.mul_pos hm hv1
        have hvle : (v : ℝ) ≤ 4 * X / (m : ℝ) :=
          (Nat.cast_le.mpr hv2).trans (Nat.floor_le h4Xm)
        have hmvX : ((m * v : ℕ) : ℝ) ≤ 4 * X := by
          rw [Nat.cast_mul]
          exact (le_div_iff₀' hmR).mp hvle
        have hF := hc x hxc I.S I.slots (m * v) hmv1 (hmvX.trans h4X)
        rw [Int.toNat_natCast, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hF 2
      calc ∑ v ∈ Finset.Icc 1 ⌊4 * X / (m : ℝ)⌋₊,
            centeredCore D.q D.𝔞 x I.S ((m * v : ℕ) : ℤ).toNat ^ 2
          ≤ ∑ _v ∈ Finset.Icc 1 ⌊4 * X / (m : ℝ)⌋₊, B ^ 2 := Finset.sum_le_sum hterm
        _ = (⌊4 * X / (m : ℝ)⌋₊ : ℝ) * B ^ 2 := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        _ ≤ 4 * X / (m : ℝ) * B ^ 2 :=
            mul_le_mul_of_nonneg_right (Nat.floor_le h4Xm) (sq_nonneg _)
        _ = 4 * X * B ^ 2 / (m : ℝ) := by ring
    · calc 4 * X * B ^ 2 = X * (4 * B ^ 2) := by ring
        _ ≤ X * Real.log x := mul_le_mul_of_nonneg_left hLB hX0.le
        _ ≤ X * Real.log x ^ (2 * (max 1 (D.C * 2 + max Ad 0 + 1) / 2)) :=
            mul_le_mul_of_nonneg_left hmaxF hX0.le
  · -- the second endpoint
    refine (sum_mul_dampedMass_le I.groups J D.q₀_pos D.q₀_lt_one (wideWindow X)
      (fun n : ℤ => ‖I.G n.toNat‖ ^ 2) (fun n => sq_nonneg _)
      (R := (Real.log x ^ D.C) ^ 2 *
        (Cd * 8 * ((3 : ℝ) ^ max Ad 0 * Real.log x ^ max Ad 0)) * X) ?_).trans ?_
    · intro m hm hfac
      have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := Nat.one_le_cast.mpr hm
      refine (sum_wideWindow_dvd_le (a := fun n : ℤ => ‖I.G n.toNat‖ ^ 2)
        (fun n => sq_nonneg _) hX1 hm).trans ?_
      have hterm : ∀ v ∈ Finset.Icc 1 ⌊4 * X / (m : ℝ)⌋₊,
          ‖I.G ((m * v : ℕ) : ℤ).toNat‖ ^ 2 ≤
            (Real.log x ^ D.C) ^ 2 * (v.divisors.card : ℝ) ^ (⌈D.C⌉₊ * 2) := by
        intro v hv
        have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1
        have hG : ‖I.G (m * v)‖ ≤ Real.log x ^ D.C * (v.divisors.card : ℝ) ^ ⌈D.C⌉₊ :=
          norm_core_mul_le I.core hL0.le hm hv1 hfac
        rw [Int.toNat_natCast]
        calc ‖I.G (m * v)‖ ^ 2
            ≤ (Real.log x ^ D.C * (v.divisors.card : ℝ) ^ ⌈D.C⌉₊) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hG 2
          _ = (Real.log x ^ D.C) ^ 2 * (v.divisors.card : ℝ) ^ (⌈D.C⌉₊ * 2) := by ring
      by_cases hcase : 1 ≤ 4 * X / (m : ℝ)
      · -- the range of `v` is nonempty: the divisor moment on `v ≤ 8X/m`
        have hdouble : 8 * X / (m : ℝ) = 2 * (4 * X / (m : ℝ)) := by ring
        have hY2 : 2 ≤ 8 * X / (m : ℝ) := by
          rw [hdouble]
          linarith
        have hYle : 8 * X / (m : ℝ) ≤ 8 * X := div_le_self (by linarith) hm1
        have hsub : Finset.Icc 1 ⌊4 * X / (m : ℝ)⌋₊ ⊆ Finset.Icc 1 ⌊8 * X / (m : ℝ)⌋₊ := by
          refine Finset.Icc_subset_Icc le_rfl (Nat.floor_mono ?_)
          rw [hdouble]
          linarith
        have hlog1 : 1 ≤ Real.log (2 * (8 * X / (m : ℝ))) := by
          rw [Real.le_log_iff_exp_le (by linarith)]
          have h := Real.exp_one_lt_three
          linarith
        have hlog2 : Real.log (2 * (8 * X / (m : ℝ))) ≤ 3 * Real.log x := by
          have h : 2 * (8 * X / (m : ℝ)) ≤ x ^ 3 := by linarith
          calc Real.log (2 * (8 * X / (m : ℝ))) ≤ Real.log (x ^ 3) :=
                Real.log_le_log (by linarith) h
            _ = 3 * Real.log x := by
                rw [Real.log_pow]
                norm_num
        have hlogA : Real.log (2 * (8 * X / (m : ℝ))) ^ Ad ≤
            (3 : ℝ) ^ max Ad 0 * Real.log x ^ max Ad 0 :=
          calc Real.log (2 * (8 * X / (m : ℝ))) ^ Ad
              ≤ Real.log (2 * (8 * X / (m : ℝ))) ^ max Ad 0 :=
                Real.rpow_le_rpow_of_exponent_le hlog1 (le_max_left _ _)
            _ ≤ (3 * Real.log x) ^ max Ad 0 :=
                Real.rpow_le_rpow (zero_le_one.trans hlog1) hlog2 (le_max_right _ _)
            _ = (3 : ℝ) ^ max Ad 0 * Real.log x ^ max Ad 0 :=
                Real.mul_rpow (by norm_num) hL0.le
        calc ∑ v ∈ Finset.Icc 1 ⌊4 * X / (m : ℝ)⌋₊, ‖I.G ((m * v : ℕ) : ℤ).toNat‖ ^ 2
            ≤ ∑ v ∈ Finset.Icc 1 ⌊4 * X / (m : ℝ)⌋₊,
                (Real.log x ^ D.C) ^ 2 * (v.divisors.card : ℝ) ^ (⌈D.C⌉₊ * 2) :=
              Finset.sum_le_sum hterm
          _ ≤ ∑ v ∈ Finset.Icc 1 ⌊8 * X / (m : ℝ)⌋₊,
                (Real.log x ^ D.C) ^ 2 * (v.divisors.card : ℝ) ^ (⌈D.C⌉₊ * 2) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun v _ _ =>
                mul_nonneg (sq_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
          _ = (Real.log x ^ D.C) ^ 2 *
                ∑ v ∈ Finset.Icc 1 ⌊8 * X / (m : ℝ)⌋₊,
                  (v.divisors.card : ℝ) ^ (⌈D.C⌉₊ * 2) := by
              rw [Finset.mul_sum]
          _ ≤ (Real.log x ^ D.C) ^ 2 *
                (Cd * (8 * X / (m : ℝ)) * Real.log (2 * (8 * X / (m : ℝ))) ^ Ad) :=
              mul_le_mul_of_nonneg_left (hdiv (8 * X / (m : ℝ)) (by linarith)) (sq_nonneg _)
          _ ≤ (Real.log x ^ D.C) ^ 2 *
                (Cd * (8 * X / (m : ℝ)) * ((3 : ℝ) ^ max Ad 0 * Real.log x ^ max Ad 0)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hlogA (mul_nonneg hCd.le (by linarith)))
                (sq_nonneg _)
          _ = (Real.log x ^ D.C) ^ 2 *
                (Cd * 8 * ((3 : ℝ) ^ max Ad 0 * Real.log x ^ max Ad 0)) * X / (m : ℝ) := by
              ring
      · -- no multiple of `m` in the dyad
        have hfl : ⌊4 * X / (m : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr (not_le.mp hcase)
        have hempty : Finset.Icc 1 ⌊4 * X / (m : ℝ)⌋₊ = ∅ := by
          rw [hfl]
          exact Finset.Icc_eq_empty (by norm_num)
        rw [hempty, Finset.sum_empty]
        exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
          (mul_nonneg (mul_nonneg hCd.le (by norm_num))
            (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hrp _)))) hX0.le) hmR.le
    · calc (Real.log x ^ D.C) ^ 2 *
            (Cd * 8 * ((3 : ℝ) ^ max Ad 0 * Real.log x ^ max Ad 0)) * X
          = X * ((Cd * 8 * (3 : ℝ) ^ max Ad 0) *
              (Real.log x ^ (D.C * 2) * Real.log x ^ max Ad 0)) := by
            rw [← hsq]
            ring
        _ ≤ X * (Real.log x * (Real.log x ^ (D.C * 2) * Real.log x ^ max Ad 0)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hLD (mul_nonneg (hrp _) (hrp _))) hX0.le
        _ = X * Real.log x ^ (D.C * 2 + max Ad 0 + 1) := by
            rw [hEG]
            ring
        _ ≤ X * Real.log x ^ (2 * (max 1 (D.C * 2 + max Ad 0 + 1) / 2)) :=
            mul_le_mul_of_nonneg_left hmaxG hX0.le

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
