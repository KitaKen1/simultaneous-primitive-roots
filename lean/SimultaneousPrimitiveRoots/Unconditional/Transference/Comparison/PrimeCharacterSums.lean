module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.PrimeCharacterPartial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Reciprocal prime sums of a nonprincipal character

Source: `verification/stage7-sources/S-03.tex`, lines 218–237 (`[S-03:0218–0237]`).

`reciprocalPrimeCharacterSum_of_siegelWalfisz :
  Supply.SiegelWalfiszPrimeCounting → ReciprocalPrimeCharacterSum` (`Comparison/Leaves.lean`).

"Partial summation on any subinterval of `[y, ∞)` bounds its reciprocal-prime sum by
`O_K((log y)^{-K} + ∫_y^∞ dt / (t (log t)^K)) = O_K((log y)^{1-K})`."

Proof. Fix `K, C`. The Siegel–Walfisz theorem is used with the modulus exponent `C + 1` and the
accuracy exponent `C + K + 3` (`PrimeSums.primeCharSum_le_of_siegelWalfisz`). Put `z = y - 2` and
`ℓ = log z`; all heights that occur are at least `z`. For `y` large, `log y ≤ 2ℓ` and
`2^C ≤ ℓ`, so that `q ≤ (log y)^C ≤ ℓ^{C+1}` (`PrimeSums.modulus_le`), and for every integer
`n ≥ z + 1`,
`|A_ρ(n)| ≤ q M₁ n (log n)^{-(C+K+3)} ≤ B n / (log n)²` with `B = M₁ ℓ^{-K}`
(`PrimeSums.rpow_saving`).

Partial summation (`PrimeSums.abel_bound`, by induction on the upper end) gives, for
`lo = m + 1 ≤ n`,
`∑_{lo ≤ p ≤ n} ρ(p)/p = A(n)/n - A(m)/m + ∑_{m ≤ k < n} A(k) (1/k - 1/(k+1))`.
The tail is bounded without integrals: `|A(k)| (1/k - 1/(k+1)) ≤ B / (k (log k)²) ≤
B (1/log(k-1) - 1/log k)` (`PrimeSums.telescope_step`), which telescopes. Hence the reciprocal sum
is at most `3B` (`PrimeSums.norm_recipSum_le`), uniformly in the upper end, and
`ℓ^{-K} ≤ 2^K (log y)^{-K}` (`PrimeSums.rpow_neg_le`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace PrimeSums

/-! ### Powers of logarithms -/

/-- The modulus condition at a lower height: `Q ≤ L^C`, `L ≤ 2ℓ`, `2^C ≤ ℓ` give
`Q ≤ ℓ^{C+1}`. -/
theorem modulus_le {Q L ℓ C : ℝ} (hC : 0 < C) (hL0 : 0 ≤ L) (hQ : Q ≤ L ^ C) (hL : L ≤ 2 * ℓ)
    (hℓ : (2 : ℝ) ^ C ≤ ℓ) (hℓ0 : 0 < ℓ) : Q ≤ ℓ ^ (C + 1) := by
  have h1 : L ^ C ≤ (2 * ℓ) ^ C := Real.rpow_le_rpow hL0 hL hC.le
  have h2 : (2 * ℓ) ^ C = (2 : ℝ) ^ C * ℓ ^ C := Real.mul_rpow zero_le_two hℓ0.le
  have h3 : ℓ ^ (C + 1) = ℓ ^ C * ℓ := Real.rpow_add_one hℓ0.ne' C
  have h4 : 0 ≤ ℓ ^ C := Real.rpow_nonneg hℓ0.le C
  have h5 : (2 : ℝ) ^ C * ℓ ^ C ≤ ℓ * ℓ ^ C := mul_le_mul_of_nonneg_right hℓ h4
  rw [h3]
  linarith

/-- Spending the accuracy exponent `C + 1 + K + 2`: for `1 ≤ ℓ ≤ x` and `Q ≤ ℓ^{C+1}`,
`Q x^{-(C+1+K+2)} ≤ ℓ^{-K} / x²`. -/
theorem rpow_saving {ℓ x Q C K : ℝ} (hℓ : 1 ≤ ℓ) (hx : ℓ ≤ x) (hC : 0 < C) (hK : 0 < K)
    (hQ : Q ≤ ℓ ^ (C + 1)) :
    Q * x ^ (-(C + 1 + K + 2)) ≤ ℓ ^ (-K) * (x⁻¹) ^ 2 := by
  have hℓ0 : 0 < ℓ := by linarith
  have hx0 : 0 < x := by linarith
  have h1 : Q ≤ x ^ (C + 1) := hQ.trans (Real.rpow_le_rpow hℓ0.le hx (by linarith))
  have h2 : x ^ (C + 1) * x ^ (-(C + 1 + K + 2)) = x ^ (-K) * (x⁻¹) ^ 2 := by
    have e : C + 1 + -(C + 1 + K + 2) = -K + -(2 : ℝ) := by ring
    rw [← Real.rpow_add hx0, e, Real.rpow_add hx0, Real.rpow_neg hx0.le (2 : ℝ), Real.rpow_two,
      inv_pow]
  have h3 : x ^ (-K) ≤ ℓ ^ (-K) := Real.rpow_le_rpow_of_nonpos hℓ0 hx (by linarith)
  have h4 : 0 ≤ x ^ (-(C + 1 + K + 2)) := Real.rpow_nonneg hx0.le _
  have h5 : 0 ≤ (x⁻¹) ^ 2 := sq_nonneg _
  calc Q * x ^ (-(C + 1 + K + 2)) ≤ x ^ (C + 1) * x ^ (-(C + 1 + K + 2)) :=
        mul_le_mul_of_nonneg_right h1 h4
    _ = x ^ (-K) * (x⁻¹) ^ 2 := h2
    _ ≤ ℓ ^ (-K) * (x⁻¹) ^ 2 := mul_le_mul_of_nonneg_right h3 h5

/-- `ℓ^{-K} ≤ 2^K L^{-K}` if `0 < L ≤ 2ℓ`. -/
theorem rpow_neg_le {L ℓ K : ℝ} (hK : 0 < K) (hL0 : 0 < L) (hL : L ≤ 2 * ℓ) :
    ℓ ^ (-K) ≤ (2 : ℝ) ^ K * L ^ (-K) := by
  have h1 : ℓ ^ (-K) ≤ (L / 2) ^ (-K) :=
    Real.rpow_le_rpow_of_nonpos (half_pos hL0) (by linarith) (by linarith)
  have h2 : (L / 2) ^ (-K) = L ^ (-K) / (2 : ℝ) ^ (-K) := Real.div_rpow hL0.le zero_le_two _
  have h3 : (2 : ℝ) ^ (-K) = ((2 : ℝ) ^ K)⁻¹ := Real.rpow_neg zero_le_two K
  rw [h2, h3, div_inv_eq_mul] at h1
  linarith

/-! ### The telescoping inequality -/

/-- The algebra of the telescoping step, with the inverses as variables: `u = 1/x`,
`v = 1/(x+1)`, `ia = 1/a`, `ib = 1/b`, where `a = log(x - 1)` and `b = log x`
(`a ≤ b` follows from `u ≤ b - a`). -/
theorem telescope_alg {B An x u v a b ia ib : ℝ} (hB : 0 ≤ B) (hAn0 : 0 ≤ An)
    (hu1 : x * u = 1) (hv1 : (x + 1) * v = 1) (hu0 : 0 < u) (hv0 : 0 < v)
    (hia1 : a * ia = 1) (hib1 : b * ib = 1) (hia0 : 0 < ia) (hib0 : 0 < ib)
    (hlog : u ≤ b - a) (hA : An ≤ B * x * ib ^ 2) :
    An * (u - v) ≤ B * (ia - ib) := by
  have huv : u - v = u * v := by linear_combination (-u) * hv1 + v * hu1
  have hvu : v ≤ u := by
    have h : 0 < u * v := mul_pos hu0 hv0
    linarith
  have hw : u - v ≤ u * u := by
    rw [huv]
    exact mul_le_mul_of_nonneg_left hvu hu0.le
  have hw0 : 0 ≤ u - v := by linarith
  have h1 : An * (u - v) ≤ B * x * ib ^ 2 * (u * u) :=
    (mul_le_mul_of_nonneg_right hA hw0).trans
      (mul_le_mul_of_nonneg_left hw (hAn0.trans hA))
  have h2 : B * x * ib ^ 2 * (u * u) = B * (u * ib ^ 2) := by
    linear_combination (B * ib ^ 2 * u) * hu1
  have h3 : ia - ib = (b - a) * (ia * ib) := by
    linear_combination (-ia) * hib1 + ib * hia1
  have hiab : ib ≤ ia := by
    have h : 0 ≤ (b - a) * (ia * ib) := mul_nonneg (by linarith) (mul_pos hia0 hib0).le
    linarith
  have e1 : u * (ia * ib) ≤ (b - a) * (ia * ib) :=
    mul_le_mul_of_nonneg_right hlog (mul_pos hia0 hib0).le
  have e2 : u * (ib * ib) ≤ u * (ia * ib) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hiab hib0.le) hu0.le
  have h4 : u * ib ^ 2 ≤ ia - ib := by linarith
  calc An * (u - v) ≤ B * x * ib ^ 2 * (u * u) := h1
    _ = B * (u * ib ^ 2) := h2
    _ ≤ B * (ia - ib) := mul_le_mul_of_nonneg_left h4 hB

/-- **The telescoping step**: if `A ≤ B x / (log x)²`, then
`A (1/x - 1/(x+1)) ≤ B (1/log(x-1) - 1/log x)`. -/
theorem telescope_step {B An x : ℝ} (hB : 0 ≤ B) (hAn0 : 0 ≤ An) (hx : 2 ≤ x)
    (ha : 0 < Real.log (x - 1)) (hA : An ≤ B * x * ((Real.log x)⁻¹) ^ 2) :
    An * (x⁻¹ - (x + 1)⁻¹) ≤ B * ((Real.log (x - 1))⁻¹ - (Real.log x)⁻¹) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hx2 : 0 < x + 1 := by linarith
  have hu1 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0.ne'
  have hv1 : (x + 1) * (x + 1)⁻¹ = 1 := mul_inv_cancel₀ hx2.ne'
  have hu0 : 0 < x⁻¹ := inv_pos.mpr hx0
  have hv0 : 0 < (x + 1)⁻¹ := inv_pos.mpr hx2
  have hlog : x⁻¹ ≤ Real.log x - Real.log (x - 1) := by
    have h := Real.log_le_sub_one_of_pos (mul_pos hx1 hu0)
    rw [Real.log_mul hx1.ne' hu0.ne', Real.log_inv] at h
    have h' : (x - 1) * x⁻¹ - 1 = -x⁻¹ := by linear_combination hu1
    linarith
  have hb : 0 < Real.log x := by linarith
  exact telescope_alg hB hAn0 hu1 hv1 hu0 hv0 (mul_inv_cancel₀ ha.ne')
    (mul_inv_cancel₀ hb.ne') (inv_pos.mpr ha) (inv_pos.mpr hb) hlog hA

/-! ### Partial summation -/

/-- **Partial summation with a telescoping majorant.** Let `S (n + 1) = S n +
(A (n + 1) - A n) / (n + 1)` for `n ≥ m`, `S m = 0`, and suppose that
`|A n| (1/n - 1/(n+1)) ≤ B (τ n - τ (n + 1))`. Then
`|S n - A n / n + A m / m| ≤ B (τ m - τ n)` for all `n ≥ m`. -/
theorem abel_bound (A S : ℕ → ℂ) (τ : ℕ → ℝ) (B : ℝ) (m : ℕ) (hS0 : S m = 0)
    (hS : ∀ n, m ≤ n → S (n + 1) = S n + (A (n + 1) - A n) / ((n : ℂ) + 1))
    (hw : ∀ n, m ≤ n → 0 ≤ (n : ℝ)⁻¹ - ((n : ℝ) + 1)⁻¹)
    (hstep : ∀ n, m ≤ n →
      ‖A n‖ * ((n : ℝ)⁻¹ - ((n : ℝ) + 1)⁻¹) ≤ B * (τ n - τ (n + 1))) :
    ∀ n, m ≤ n → ‖S n - A n / (n : ℂ) + A m / (m : ℂ)‖ ≤ B * (τ m - τ n) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    have h : S m - A m / (m : ℂ) + A m / (m : ℂ) = 0 := by
      rw [hS0]
      ring
    exact le_of_eq (by rw [h, norm_zero, sub_self, mul_zero])
  | succ n hmn ih =>
    have h : S (n + 1) - A (n + 1) / ((n + 1 : ℕ) : ℂ) + A m / (m : ℂ) =
        (S n - A n / (n : ℂ) + A m / (m : ℂ)) +
          A n * (((n : ℝ)⁻¹ - ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) := by
      rw [hS n hmn]
      push_cast
      ring
    have t1 := norm_add_le (S n - A n / (n : ℂ) + A m / (m : ℂ))
      (A n * (((n : ℝ)⁻¹ - ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ))
    have t2 : ‖A n * (((n : ℝ)⁻¹ - ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)‖ =
        ‖A n‖ * ((n : ℝ)⁻¹ - ((n : ℝ) + 1)⁻¹) := by
      rw [norm_mul, Complex.norm_of_nonneg (hw n hmn)]
    have t3 := hstep n hmn
    rw [h]
    linarith

/-- The reciprocal sum of `ρ` over the primes in `[m + 1, n]`. -/
def recipSum {q : ℕ} (ρ : DirichletCharacter ℂ q) (m n : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc (m + 1) n, if k.Prime then ρ (k : ZMod q) / (k : ℂ) else 0

theorem recipSum_of_lt {q : ℕ} (ρ : DirichletCharacter ℂ q) {m n : ℕ} (h : n < m + 1) :
    recipSum ρ m n = 0 := by
  unfold recipSum
  rw [Finset.Icc_eq_empty_of_lt h, Finset.sum_empty]

theorem recipSum_succ {q : ℕ} (ρ : DirichletCharacter ℂ q) {m n : ℕ} (hmn : m ≤ n) :
    recipSum ρ m (n + 1) =
      recipSum ρ m n + (primeCharSum ρ (n + 1) - primeCharSum ρ n) / ((n : ℂ) + 1) := by
  unfold recipSum
  rw [Finset.sum_Icc_succ_top (Nat.add_le_add_right hmn 1), primeCharSum_succ]
  congr 1
  split_ifs with hp
  · rw [add_sub_cancel_left, (Nat.cast_add_one n : ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1)]
  · rw [add_zero, sub_self, zero_div]

theorem recipSum_eq_filter {q : ℕ} (ρ : DirichletCharacter ℂ q) (m n : ℕ) :
    ∑ p ∈ (Finset.Icc (m + 1) n).filter Nat.Prime, ρ (p : ZMod q) / (p : ℂ) =
      recipSum ρ m n := by
  unfold recipSum
  exact Finset.sum_filter _ _

/-- **The reciprocal sum is at most `3B`**, uniformly in the upper end, if
`|A_ρ(k)| ≤ B k / (log k)²` at all heights `k ≥ z + 1` and `log z ≥ 1`. -/
theorem norm_recipSum_le {q : ℕ} (ρ : DirichletCharacter ℂ q) {B z : ℝ} (hB : 0 ≤ B)
    (hz1 : 1 ≤ z) (hz : 1 ≤ Real.log z)
    (hA : ∀ k : ℕ, z ≤ (k : ℝ) - 1 →
      ‖primeCharSum ρ k‖ ≤ B * (k : ℝ) * ((Real.log (k : ℝ))⁻¹) ^ 2)
    {m n : ℕ} (hm : z ≤ (m : ℝ) - 1) (hmn : m ≤ n) :
    ‖recipSum ρ m n‖ ≤ 3 * B := by
  have hz0 : 0 < z := by linarith
  -- the heights `k ≥ m` and their logarithms
  have hk : ∀ k : ℕ, m ≤ k → z ≤ (k : ℝ) - 1 := by
    intro k hmk
    have h : (m : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hmk
    linarith
  have hloga : ∀ k : ℕ, m ≤ k → 1 ≤ Real.log ((k : ℝ) - 1) := fun k hmk =>
    hz.trans (Real.log_le_log hz0 (hk k hmk))
  have hlogb : ∀ k : ℕ, m ≤ k → 1 ≤ Real.log (k : ℝ) := by
    intro k hmk
    have h1 : 0 < (k : ℝ) - 1 := by linarith [hk k hmk]
    have h2 : Real.log ((k : ℝ) - 1) ≤ Real.log (k : ℝ) := Real.log_le_log h1 (by linarith)
    linarith [hloga k hmk]
  -- the steps of the partial summation
  have hw : ∀ k : ℕ, m ≤ k → 0 ≤ (k : ℝ)⁻¹ - ((k : ℝ) + 1)⁻¹ := by
    intro k hmk
    have hk0 : 0 < (k : ℝ) := by linarith [hk k hmk]
    exact sub_nonneg.mpr (inv_anti₀ hk0 (by linarith))
  have hstep : ∀ k : ℕ, m ≤ k → ‖primeCharSum ρ k‖ * ((k : ℝ)⁻¹ - ((k : ℝ) + 1)⁻¹) ≤
      B * ((Real.log ((k : ℝ) - 1))⁻¹ - (Real.log (((k + 1 : ℕ) : ℝ) - 1))⁻¹) := by
    intro k hmk
    have hcast : ((k + 1 : ℕ) : ℝ) - 1 = (k : ℝ) := by
      rw [Nat.cast_add_one]
      ring
    have h2 : (2 : ℝ) ≤ (k : ℝ) := by linarith [hk k hmk]
    have ha : 0 < Real.log ((k : ℝ) - 1) := by linarith [hloga k hmk]
    rw [hcast]
    exact telescope_step hB (norm_nonneg _) h2 ha (hA k (hk k hmk))
  have hab : ‖recipSum ρ m n - primeCharSum ρ n / (n : ℂ) + primeCharSum ρ m / (m : ℂ)‖ ≤
      B * ((Real.log ((m : ℝ) - 1))⁻¹ - (Real.log ((n : ℝ) - 1))⁻¹) :=
    abel_bound (primeCharSum ρ) (recipSum ρ m) (fun k : ℕ => (Real.log ((k : ℝ) - 1))⁻¹) B m
      (recipSum_of_lt ρ (Nat.lt_add_one m)) (fun k hmk => recipSum_succ ρ hmk) hw hstep n hmn
  -- the boundary terms
  have hbdry : ∀ k : ℕ, m ≤ k → ‖primeCharSum ρ k / (k : ℂ)‖ ≤ B := by
    intro k hmk
    have hk0 : 0 < (k : ℝ) := by linarith [hk k hmk]
    have hib : (Real.log (k : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hlogb k hmk)
    have hib0 : 0 ≤ (Real.log (k : ℝ))⁻¹ := inv_nonneg.mpr (by linarith [hlogb k hmk])
    have hsq : ((Real.log (k : ℝ))⁻¹) ^ 2 ≤ 1 := pow_le_one₀ hib0 hib
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ hk0]
    calc ‖primeCharSum ρ k‖ ≤ B * (k : ℝ) * ((Real.log (k : ℝ))⁻¹) ^ 2 := hA k (hk k hmk)
      _ ≤ B * (k : ℝ) * 1 := mul_le_mul_of_nonneg_left hsq (mul_nonneg hB hk0.le)
      _ = B * (k : ℝ) := mul_one _
  have hτm : (Real.log ((m : ℝ) - 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hloga m le_rfl)
  have hτn : 0 ≤ (Real.log ((n : ℝ) - 1))⁻¹ := inv_nonneg.mpr (by linarith [hloga n hmn])
  have h1 := hbdry n hmn
  have h2 := hbdry m le_rfl
  have h3 : B * ((Real.log ((m : ℝ) - 1))⁻¹ - (Real.log ((n : ℝ) - 1))⁻¹) ≤ B * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) hB
  have t1 := norm_sub_le
    ((recipSum ρ m n - primeCharSum ρ n / (n : ℂ) + primeCharSum ρ m / (m : ℂ)) +
      primeCharSum ρ n / (n : ℂ)) (primeCharSum ρ m / (m : ℂ))
  have t2 := norm_add_le
    (recipSum ρ m n - primeCharSum ρ n / (n : ℂ) + primeCharSum ρ m / (m : ℂ))
    (primeCharSum ρ n / (n : ℂ))
  have hdecomp : recipSum ρ m n =
      (recipSum ρ m n - primeCharSum ρ n / (n : ℂ) + primeCharSum ρ m / (m : ℂ)) +
        primeCharSum ρ n / (n : ℂ) - primeCharSum ρ m / (m : ℂ) := by ring
  rw [hdecomp]
  linarith

/-- **The reciprocal prime sum**, from the bound for the partial sums at heights `≥ y₁`. -/
theorem final_bound {K C M₁ y₁ : ℝ} (hK : 0 < K) (hC : 0 < C) (hM₁ : 0 < M₁)
    (h₁ : ∀ q : ℕ, 0 < q → ∀ ρ : DirichletCharacter ℂ q, ρ ≠ 1 → ∀ n : ℕ, y₁ ≤ (n : ℝ) →
      (q : ℝ) ≤ Real.log (n : ℝ) ^ (C + 1) →
      ‖primeCharSum ρ n‖ ≤
        (q : ℝ) * (M₁ * (n : ℝ) * Real.log (n : ℝ) ^ (-(C + 1 + K + 2))))
    {y : ℝ} (hy : |y₁| + 6 + Real.exp (1 + (2 : ℝ) ^ C) ≤ y) {q : ℕ} (hq : 0 < q)
    (hqy : (q : ℝ) ≤ Real.log y ^ C) (ρ : DirichletCharacter ℂ q) (hρ : ρ ≠ 1) (lo hi : ℕ)
    (hlo : y ≤ (lo : ℝ)) :
    ‖∑ p ∈ (Finset.Icc lo hi).filter Nat.Prime, ρ (p : ZMod q) / (p : ℂ)‖ ≤
      3 * M₁ * (2 : ℝ) ^ K * Real.log y ^ (-K) := by
  -- the height `z = y - 2` and its logarithm
  have hE : 0 < Real.exp (1 + (2 : ℝ) ^ C) := Real.exp_pos _
  have h2C : 0 < (2 : ℝ) ^ C := Real.rpow_pos_of_pos two_pos C
  have hy₁ : y₁ ≤ |y₁| := le_abs_self y₁
  have hy₁0 : 0 ≤ |y₁| := abs_nonneg y₁
  have hzE : Real.exp (1 + (2 : ℝ) ^ C) ≤ y - 2 := by linarith
  have hz0 : 0 < y - 2 := by linarith
  have hz1 : 1 ≤ y - 2 := by linarith
  have hℓ : 1 + (2 : ℝ) ^ C ≤ Real.log (y - 2) := by
    have h := Real.log_le_log hE hzE
    rwa [Real.log_exp] at h
  have hℓ1 : 1 ≤ Real.log (y - 2) := by linarith
  -- `log y ≤ 2 log(y - 2)`
  have hy0 : 0 < y := by linarith
  have hsq : y ≤ (y - 2) * (y - 2) := by
    have h : 0 ≤ (y - 1) * (y - 4) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hlogy : Real.log y ≤ 2 * Real.log (y - 2) := by
    have h := Real.log_le_log hy0 hsq
    rw [Real.log_mul hz0.ne' hz0.ne'] at h
    linarith
  have hlogy0 : 0 < Real.log y := Real.log_pos (by linarith)
  -- the modulus condition at all heights `≥ y - 2`
  have hqℓ : (q : ℝ) ≤ Real.log (y - 2) ^ (C + 1) :=
    modulus_le hC hlogy0.le hqy hlogy (by linarith) (by linarith)
  -- the bound for the partial sums
  have hB : 0 ≤ M₁ * Real.log (y - 2) ^ (-K) :=
    mul_nonneg hM₁.le (Real.rpow_nonneg (by linarith) _)
  have hA : ∀ n : ℕ, y - 2 ≤ (n : ℝ) - 1 → ‖primeCharSum ρ n‖ ≤
      M₁ * Real.log (y - 2) ^ (-K) * (n : ℝ) * ((Real.log (n : ℝ))⁻¹) ^ 2 := by
    intro n hn
    have hn0 : 0 < (n : ℝ) := by linarith
    have hℓn : Real.log (y - 2) ≤ Real.log (n : ℝ) := Real.log_le_log hz0 (by linarith)
    have hqn : (q : ℝ) ≤ Real.log (n : ℝ) ^ (C + 1) :=
      hqℓ.trans (Real.rpow_le_rpow (by linarith) hℓn (by linarith))
    have h := h₁ q hq ρ hρ n (by linarith) hqn
    have hsave := rpow_saving hℓ1 hℓn hC hK hqℓ
    have hMn : 0 ≤ M₁ * (n : ℝ) := mul_nonneg hM₁.le hn0.le
    calc ‖primeCharSum ρ n‖
        ≤ (q : ℝ) * (M₁ * (n : ℝ) * Real.log (n : ℝ) ^ (-(C + 1 + K + 2))) := h
      _ = M₁ * (n : ℝ) * ((q : ℝ) * Real.log (n : ℝ) ^ (-(C + 1 + K + 2))) := by ring
      _ ≤ M₁ * (n : ℝ) * (Real.log (y - 2) ^ (-K) * ((Real.log (n : ℝ))⁻¹) ^ 2) :=
          mul_le_mul_of_nonneg_left hsave hMn
      _ = M₁ * Real.log (y - 2) ^ (-K) * (n : ℝ) * ((Real.log (n : ℝ))⁻¹) ^ 2 := by ring
  -- back to `log y`
  have h3B : 3 * (M₁ * Real.log (y - 2) ^ (-K)) ≤
      3 * M₁ * (2 : ℝ) ^ K * Real.log y ^ (-K) := by
    have h := mul_le_mul_of_nonneg_left (rpow_neg_le hK hlogy0 hlogy)
      (mul_nonneg zero_le_three hM₁.le)
    linarith
  -- `lo = m + 1`
  have hlo1 : 1 ≤ lo := by
    have h : (1 : ℝ) ≤ (lo : ℝ) := by linarith
    exact_mod_cast h
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, lo = m + 1 := ⟨lo - 1, by omega⟩
  have hm : y - 2 ≤ (m : ℝ) - 1 := by
    rw [Nat.cast_add_one] at hlo
    linarith
  rw [recipSum_eq_filter]
  rcases Nat.lt_or_ge hi m with hmh | hmh
  · have hlt : hi < m + 1 := by omega
    rw [recipSum_of_lt ρ hlt, norm_zero]
    linarith
  · exact (norm_recipSum_le ρ hB hz1 hℓ1 hA hm hmh).trans h3B

end PrimeSums

/-- **Reciprocal prime sums of a nonprincipal character** [S-03:0218–0237], from the
Siegel–Walfisz theorem in prime-counting form. The constants are `M = 3 M₁ 2^K` and
`y₀ = |y₁| + 6 + exp(1 + 2^C)`, where `M₁, y₁` are the Siegel–Walfisz constants for the accuracy
exponent `C + K + 3` and the modulus exponent `C + 1`. -/
theorem reciprocalPrimeCharacterSum_of_siegelWalfisz :
    Supply.SiegelWalfiszPrimeCounting → ReciprocalPrimeCharacterSum := by
  intro hSW K C hK hC
  obtain ⟨M₁, hM₁, y₁, h₁⟩ := PrimeSums.primeCharSum_le_of_siegelWalfisz hSW
    (C + 1 + K + 2) (C + 1) (by linarith) (by linarith)
  refine ⟨3 * M₁ * (2 : ℝ) ^ K, |y₁| + 6 + Real.exp (1 + (2 : ℝ) ^ C), ?_⟩
  intro y hy q hq hqy ρ hρ lo hi hlo
  exact PrimeSums.final_bound hK hC hM₁ h₁ hy hq hqy ρ hρ lo hi hlo

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
