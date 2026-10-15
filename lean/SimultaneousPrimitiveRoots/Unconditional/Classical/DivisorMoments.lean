module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.NatDivisors
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Moments of the divisor function

The divisor-moment bounds of `lem:moment-bounds` (`verification/stage7-sources/P-02.tex`,
lines 73--93) and `lem:divisor-moments` (`verification/stage7-sources/S-01.tex`, lines 159--172):
for every fixed `k : ℕ` there are constants `C > 0` and `A` such that for all real `Y ≥ 1`

* `∑_{n ≤ Y} τ(n)^k ≤ C · Y · (log (2Y))^A` (`sum_divisorCount_pow_le`),
* `∑_{n ≤ Y} τ(n)^k / n ≤ C · (log (2Y))^A` (`sum_divisorCount_pow_div_le`).

Here `τ(n) = n.divisors.card`, which is `ArithmeticFunction.sigma 0 n`
(`ArithmeticFunction.sigma_zero_apply`; the statements in that form are
`sum_sigma_zero_pow_le` and `sum_sigma_zero_pow_div_le`), and the sums run over
`n ∈ Finset.Icc 1 ⌊Y⌋₊`.

## Proof

The papers bound the harmonic sum by an Euler product. We use the equally classical elementary
induction on `k`, which needs no information on primes: writing `τ(n) = ∑_{d ∣ n} 1` and using
the submultiplicativity `τ(dm) ≤ τ(d) τ(m)` (`card_divisors_mul_le`),

`∑_{n ≤ N} τ(n)^{k+1} / n = ∑_{d ≤ N} ∑_{m ≤ N/d} τ(dm)^k / (dm) ≤ (∑_{n ≤ N} τ(n)^k / n)²`

(`sum_divisorCount_pow_succ_div_le`). Together with `∑_{n ≤ N} 1/n ≤ 1 + log N` this gives the
explicit bound `∑_{n ≤ N} τ(n)^k / n ≤ (1 + log N)^(2^k)`
(`sum_divisorCount_pow_div_le_one_add_log_pow`), hence `≤ (2 log (2Y))^(2^k)` for real `Y ≥ 1`
(`sum_divisorCount_pow_div_le_explicit`). As in the papers, the counting bound follows by
multiplying by `Y` (`sum_divisorCount_pow_le_mul_sum_div`, `sum_divisorCount_pow_le_explicit`).
Both final theorems hold with `C = 2^(2^k)` and `A = 2^k`; the explicit forms should be used when
the sign of the exponent matters.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Classical

open scoped Pointwise in
/-- Submultiplicativity of the divisor function: `τ(mn) ≤ τ(m) τ(n)`. -/
theorem card_divisors_mul_le (m n : ℕ) :
    (m * n).divisors.card ≤ m.divisors.card * n.divisors.card := by
  rw [Nat.divisors_mul]
  exact Finset.card_mul_le

/-- The harmonic sum: `∑_{1 ≤ n ≤ N} 1/n ≤ 1 + log N`. -/
theorem sum_Icc_inv_le_one_add_log (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

/-- The induction step for the harmonic divisor moments:
`∑_{n ≤ N} τ(n)^{k+1} / n ≤ (∑_{n ≤ N} τ(n)^k / n)²`. -/
theorem sum_divisorCount_pow_succ_div_le (k N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ (k + 1) / (n : ℝ) ≤
      (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ k / (n : ℝ)) ^ 2 := by
  have hf0 : ∀ n : ℕ, 0 ≤ (n.divisors.card : ℝ) ^ k / (n : ℝ) := fun n => by positivity
  -- `τ(n) = ∑_{d ≤ N} [d ∣ n]` for `1 ≤ n ≤ N`
  have h1 : ∀ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ (k + 1) / (n : ℝ) =
      ∑ d ∈ Finset.Icc 1 N, if d ∣ n then (n.divisors.card : ℝ) ^ k / (n : ℝ) else 0 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hdiv : (Finset.Icc 1 N).filter (fun d => d ∣ n) = n.divisors := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨-, h⟩
        exact ⟨h, by omega⟩
      · rintro ⟨h, -⟩
        have h1 : d ≤ n := Nat.le_of_dvd (by omega) h
        have h2 : 0 < d := Nat.pos_of_dvd_of_pos h (by omega)
        exact ⟨⟨h2, by omega⟩, h⟩
    calc (n.divisors.card : ℝ) ^ (k + 1) / (n : ℝ)
        = ∑ _d ∈ n.divisors, (n.divisors.card : ℝ) ^ k / (n : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ = ∑ _d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ n),
            (n.divisors.card : ℝ) ^ k / (n : ℝ) := by
          rw [hdiv]
      _ = ∑ d ∈ Finset.Icc 1 N, if d ∣ n then (n.divisors.card : ℝ) ^ k / (n : ℝ) else 0 :=
          Finset.sum_filter _ _
  -- for fixed `d`, the multiples `n = d m` of `d` contribute at most `f(d) ∑_m f(m)`
  have key : ∀ d ∈ Finset.Icc 1 N,
      ∑ n ∈ Finset.Icc 1 N, (if d ∣ n then (n.divisors.card : ℝ) ^ k / (n : ℝ) else 0) ≤
        ∑ m ∈ Finset.Icc 1 N,
          (d.divisors.card : ℝ) ^ k / (d : ℝ) * ((m.divisors.card : ℝ) ^ k / (m : ℝ)) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    calc ∑ n ∈ Finset.Icc 1 N, (if d ∣ n then (n.divisors.card : ℝ) ^ k / (n : ℝ) else 0)
        = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => d ∣ n),
            (n.divisors.card : ℝ) ^ k / (n : ℝ) := (Finset.sum_filter _ _).symm
      _ ≤ ∑ n ∈ (Finset.Icc 1 N).image (fun m => d * m),
            (n.divisors.card : ℝ) ^ k / (n : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => hf0 n)
          intro n hn
          rw [Finset.mem_filter, Finset.mem_Icc] at hn
          obtain ⟨⟨hn1, hnN⟩, m, rfl⟩ := hn
          have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn1)
          refine Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr ⟨hm0, ?_⟩, rfl⟩
          exact (Nat.le_mul_of_pos_left m hd.1).trans hnN
      _ = ∑ m ∈ Finset.Icc 1 N, ((d * m).divisors.card : ℝ) ^ k / ((d * m : ℕ) : ℝ) := by
          refine Finset.sum_image ?_
          intro x _ y _ hxy
          exact Nat.eq_of_mul_eq_mul_left hd.1 hxy
      _ ≤ ∑ m ∈ Finset.Icc 1 N,
            (d.divisors.card : ℝ) ^ k / (d : ℝ) * ((m.divisors.card : ℝ) ^ k / (m : ℝ)) := by
          refine Finset.sum_le_sum fun m _ => ?_
          have hτ : ((d * m).divisors.card : ℝ) ≤
              (d.divisors.card : ℝ) * (m.divisors.card : ℝ) := by
            exact_mod_cast card_divisors_mul_le d m
          rw [div_mul_div_comm, ← mul_pow, Nat.cast_mul]
          gcongr
  calc ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ (k + 1) / (n : ℝ)
      = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
          if d ∣ n then (n.divisors.card : ℝ) ^ k / (n : ℝ) else 0 := Finset.sum_congr rfl h1
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          if d ∣ n then (n.divisors.card : ℝ) ^ k / (n : ℝ) else 0 := Finset.sum_comm
    _ ≤ ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          (d.divisors.card : ℝ) ^ k / (d : ℝ) * ((m.divisors.card : ℝ) ^ k / (m : ℝ)) :=
        Finset.sum_le_sum key
    _ = (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ k / (n : ℝ)) ^ 2 := by
        rw [sq, Finset.sum_mul_sum]

/-- Explicit harmonic divisor moments: `∑_{n ≤ N} τ(n)^k / n ≤ (1 + log N)^(2^k)`. -/
theorem sum_divisorCount_pow_div_le_one_add_log_pow (k N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ k / (n : ℝ) ≤
      (1 + Real.log N) ^ (2 ^ k) := by
  induction k with
  | zero => simpa using sum_Icc_inv_le_one_add_log N
  | succ k ih =>
    have h0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ k / (n : ℝ) :=
      Finset.sum_nonneg fun n _ => by positivity
    calc ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ (k + 1) / (n : ℝ)
        ≤ (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ k / (n : ℝ)) ^ 2 :=
          sum_divisorCount_pow_succ_div_le k N
      _ ≤ ((1 + Real.log N) ^ (2 ^ k)) ^ 2 := pow_le_pow_left₀ h0 ih 2
      _ = (1 + Real.log N) ^ (2 ^ (k + 1)) := by rw [← pow_mul, ← pow_succ]

/-- `1 + log Y ≤ 2 log (2Y)` for `Y ≥ 1`. -/
theorem one_add_log_le_two_mul_log_two_mul {Y : ℝ} (hY : 1 ≤ Y) :
    1 + Real.log Y ≤ 2 * Real.log (2 * Y) := by
  have h2 : (1 : ℝ) / 2 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have h0 : 0 ≤ Real.log Y := Real.log_nonneg hY
  rw [Real.log_mul two_ne_zero (zero_lt_one.trans_le hY).ne']
  linarith

/-- Explicit harmonic divisor moments for a real cutoff:
`∑_{n ≤ Y} τ(n)^k / n ≤ (2 log (2Y))^(2^k)` for `Y ≥ 1`. -/
theorem sum_divisorCount_pow_div_le_explicit (k : ℕ) {Y : ℝ} (hY : 1 ≤ Y) :
    ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ k / (n : ℝ) ≤
      (2 * Real.log (2 * Y)) ^ (2 ^ k) := by
  have hN : ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Y := Nat.floor_le (zero_le_one.trans hY)
  have hN0 : (0 : ℝ) < ((⌊Y⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.floor_pos.mpr hY
  have hlog : Real.log ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Real.log Y := Real.log_le_log hN0 hN
  have h0 : 0 ≤ Real.log ((⌊Y⌋₊ : ℕ) : ℝ) := Real.log_natCast_nonneg _
  calc ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ k / (n : ℝ)
      ≤ (1 + Real.log ((⌊Y⌋₊ : ℕ) : ℝ)) ^ (2 ^ k) :=
        sum_divisorCount_pow_div_le_one_add_log_pow k _
    _ ≤ (2 * Real.log (2 * Y)) ^ (2 ^ k) := by
        refine pow_le_pow_left₀ (by linarith) ?_ _
        linarith [one_add_log_le_two_mul_log_two_mul hY]

/-- The counting moment is at most `Y` times the harmonic moment:
`∑_{n ≤ Y} τ(n)^k ≤ Y ∑_{n ≤ Y} τ(n)^k / n`. -/
theorem sum_divisorCount_pow_le_mul_sum_div (k : ℕ) {Y : ℝ} (hY : 1 ≤ Y) :
    ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ k ≤
      Y * ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ k / (n : ℝ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hnY : (n : ℝ) ≤ Y := (Nat.cast_le.mpr hn.2).trans (Nat.floor_le (zero_le_one.trans hY))
  have hτ : (0 : ℝ) ≤ (n.divisors.card : ℝ) ^ k := by positivity
  rw [mul_div_assoc', le_div_iff₀ hn0]
  linarith [mul_le_mul_of_nonneg_right hnY hτ]

/-- Explicit counting divisor moments for a real cutoff:
`∑_{n ≤ Y} τ(n)^k ≤ Y (2 log (2Y))^(2^k)` for `Y ≥ 1`. -/
theorem sum_divisorCount_pow_le_explicit (k : ℕ) {Y : ℝ} (hY : 1 ≤ Y) :
    ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ k ≤
      Y * (2 * Real.log (2 * Y)) ^ (2 ^ k) :=
  (sum_divisorCount_pow_le_mul_sum_div k hY).trans
    (mul_le_mul_of_nonneg_left (sum_divisorCount_pow_div_le_explicit k hY)
      (zero_le_one.trans hY))

/-- **Harmonic divisor moments** (`lem:moment-bounds` in P-02, `lem:divisor-moments` in S-01):
for every `k` there are `C > 0` and `A` with `∑_{n ≤ Y} τ(n)^k / n ≤ C (log (2Y))^A` for all real
`Y ≥ 1`. One may take `C = 2^(2^k)` and `A = 2^k`. -/
theorem sum_divisorCount_pow_div_le (k : ℕ) :
    ∃ C A : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ k / (n : ℝ) ≤
        C * Real.log (2 * Y) ^ A := by
  refine ⟨2 ^ (2 ^ k), ((2 ^ k : ℕ) : ℝ), by positivity, fun Y hY => ?_⟩
  rw [Real.rpow_natCast, ← mul_pow]
  exact sum_divisorCount_pow_div_le_explicit k hY

/-- **Divisor moments** (`lem:moment-bounds` in P-02, `lem:divisor-moments` in S-01): for every
`k` there are `C > 0` and `A` with `∑_{n ≤ Y} τ(n)^k ≤ C Y (log (2Y))^A` for all real `Y ≥ 1`.
One may take `C = 2^(2^k)` and `A = 2^k`. -/
theorem sum_divisorCount_pow_le (k : ℕ) :
    ∃ C A : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ k ≤
        C * Y * Real.log (2 * Y) ^ A := by
  refine ⟨2 ^ (2 ^ k), ((2 ^ k : ℕ) : ℝ), by positivity, fun Y hY => ?_⟩
  rw [Real.rpow_natCast]
  calc ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ k
      ≤ Y * (2 * Real.log (2 * Y)) ^ (2 ^ k) := sum_divisorCount_pow_le_explicit k hY
    _ = 2 ^ (2 ^ k) * Y * Real.log (2 * Y) ^ (2 ^ k) := by
        rw [mul_pow]
        ring

/-- `sum_divisorCount_pow_div_le` with the divisor function written as
`ArithmeticFunction.sigma 0`. -/
theorem sum_sigma_zero_pow_div_le (k : ℕ) :
    ∃ C A : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (ArithmeticFunction.sigma 0 n : ℝ) ^ k / (n : ℝ) ≤
        C * Real.log (2 * Y) ^ A := by
  simpa only [ArithmeticFunction.sigma_zero_apply] using sum_divisorCount_pow_div_le k

/-- `sum_divisorCount_pow_le` with the divisor function written as
`ArithmeticFunction.sigma 0`. -/
theorem sum_sigma_zero_pow_le (k : ℕ) :
    ∃ C A : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (ArithmeticFunction.sigma 0 n : ℝ) ^ k ≤
        C * Y * Real.log (2 * Y) ^ A := by
  simpa only [ArithmeticFunction.sigma_zero_apply] using sum_divisorCount_pow_le k

end SimultaneousPrimitiveRoots.Unconditional.Classical
