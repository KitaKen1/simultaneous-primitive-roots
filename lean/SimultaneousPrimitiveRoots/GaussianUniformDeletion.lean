module

public import SimultaneousPrimitiveRoots.GaussianFiniteDeletion
public import SimultaneousPrimitiveRoots.NumberFieldDeletionLogNorm
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section
open Classical

/-- A uniform bound for a translated Gaussian lattice, without an x power. -/
def gaussianUniformRowConstant : ℝ := 4 * Real.exp ((Real.log 2) ^ 2 + 1 / 4)

theorem gaussianUniformRowConstant_pos : 0 < gaussianUniformRowConstant := by
  unfold gaussianUniformRowConstant
  positivity

theorem artinGaussianWeight_le_exp_abs (t : ℝ) :
    artinGaussianWeight t ≤
      Real.exp ((Real.log 2) ^ 2 + 1 / 4) * Real.exp (-|Real.log t|) := by
  rw [artinGaussianWeight, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (|Real.log t| - 1 / 2), sq_abs (Real.log t)]

theorem gaussianPrimePowerScalar_le_uniform_geometric {N x : ℝ}
    (hN : 2 ≤ N) (hx : 0 < x) (j k : ℕ)
    (hd : (k : ℝ) * Real.log N ≤ |((j : ℝ) + 1) * Real.log N - Real.log x|) :
    Real.log N * artinGaussianWeight (N ^ (j + 1) / x) ≤
      (Real.exp ((Real.log 2) ^ 2 + 1 / 4) * Real.log N) * (1 / 2 : ℝ) ^ k := by
  have hN0 : 0 < N := by linarith
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlog2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  have hlog : Real.log (N ^ (j + 1) / x) =
      ((j : ℝ) + 1) * Real.log N - Real.log x := by
    rw [Real.log_div (pow_ne_zero _ hN0.ne') hx.ne', Real.log_pow]
    push_cast
    rfl
  have he : Real.exp (-|Real.log (N ^ (j + 1) / x)|) ≤ (1 / 2 : ℝ) ^ k := by
    have hk : (k : ℝ) * Real.log 2 ≤ |Real.log (N ^ (j + 1) / x)| := by
      rw [hlog]
      exact (mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg k)).trans hd
    calc
      _ ≤ Real.exp (-(k : ℝ) * Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by
        rw [show -(k : ℝ) * Real.log 2 = (k : ℝ) * (-Real.log 2) by ring,
          Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        simp only [one_div]
  calc
    _ ≤ Real.log N * (Real.exp ((Real.log 2) ^ 2 + 1 / 4) *
        Real.exp (-|Real.log (N ^ (j + 1) / x)|)) :=
      mul_le_mul_of_nonneg_left (artinGaussianWeight_le_exp_abs _) hL
    _ ≤ Real.log N * (Real.exp ((Real.log 2) ^ 2 + 1 / 4) * (1 / 2 : ℝ) ^ k) := by gcongr
    _ = _ := by ring

/-- Choose the answer floor(log x / log N), then verify two geometric tails.
No Poisson summation or theta transformation is needed. -/
theorem gaussianPrimePowerScalar_tsum_le_uniform {N x : ℝ}
    (hN : 2 ≤ N) (hx : 0 < x) :
    (∑' j : ℕ, Real.log N * artinGaussianWeight (N ^ (j + 1) / x)) ≤
      gaussianUniformRowConstant * Real.log N := by
  let D := Real.exp ((Real.log 2) ^ 2 + 1 / 4)
  let L := Real.log N
  let b := Real.log x
  let f : ℕ → ℝ := fun j => Real.log N * artinGaussianWeight (N ^ (j + 1) / x)
  have hD : 0 < D := Real.exp_pos _
  have hL : 0 < L := Real.log_pos (by linarith : 1 < N)
  have hs : Summable f := gaussianPrimePowerScalar_summable hN hx (by norm_num : (0 : ℝ) < 1)
  have hg : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hm : Summable (fun j : ℕ => (D * L) * (1 / 2 : ℝ) ^ j) := hg.mul_left _
  have hmv : (∑' j : ℕ, (D * L) * (1 / 2 : ℝ) ^ j) = 2 * D * L := by
    rw [hg.tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    ring
  change (∑' j, f j) ≤ 4 * D * L
  by_cases hb : 0 ≤ b
  · let n := Nat.floor (b / L)
    have hnl : (n : ℝ) * L ≤ b :=
      (le_div_iff₀ hL).mp (Nat.floor_le (div_nonneg hb hL.le))
    have hnu : b < ((n : ℝ) + 1) * L :=
      (div_lt_iff₀ hL).mp (Nat.lt_floor_add_one (b / L))
    have hleft : (∑ j ∈ Finset.range n, f j) ≤ 2 * D * L := by
      calc
        _ ≤ ∑ j ∈ Finset.range n, (D * L) * (1 / 2 : ℝ) ^ (n - 1 - j) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjn : j < n := Finset.mem_range.mp hj
          have hjcast : (j : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : j + 1 ≤ n)
          have hjmul := mul_le_mul_of_nonneg_right hjcast hL.le
          have hsub : ((n - 1 - j : ℕ) : ℝ) = (n : ℝ) - 1 - j := by
            rw [Nat.cast_sub (by omega : j ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
          have hdist : (n - 1 - j : ℕ) * L ≤ |((j : ℝ) + 1) * L - b| := by
            rw [hsub, abs_of_nonpos (by linarith : ((j : ℝ) + 1) * L - b ≤ 0)]
            nlinarith
          exact gaussianPrimePowerScalar_le_uniform_geometric hN hx j (n - 1 - j) hdist
        _ = ∑ j ∈ Finset.range n, (D * L) * (1 / 2 : ℝ) ^ j :=
          Finset.sum_range_reflect (fun k : ℕ => (D * L) * (1 / 2 : ℝ) ^ k) n
        _ ≤ ∑' j, (D * L) * (1 / 2 : ℝ) ^ j := hm.sum_le_tsum _ (fun j _ => by positivity)
        _ = _ := hmv
    have hright : (∑' j : ℕ, f (j + n)) ≤ 2 * D * L := by
      apply le_trans (((summable_nat_add_iff n).mpr hs).tsum_le_tsum ?_ hm) hmv.le
      intro j
      have hjL : 0 ≤ (j : ℝ) * L := mul_nonneg (Nat.cast_nonneg j) hL.le
      have hdist : (j : ℝ) * L ≤ |((j + n : ℕ) + 1 : ℝ) * L - b| := by
        push_cast
        rw [abs_of_nonneg (by nlinarith)]
        nlinarith
      exact gaussianPrimePowerScalar_le_uniform_geometric hN hx (j + n) j hdist
    rw [← hs.sum_add_tsum_nat_add n]
    linarith
  · have hbneg : b < 0 := lt_of_not_ge hb
    have hwhole : (∑' j, f j) ≤ 2 * D * L := by
      apply le_trans (hs.tsum_le_tsum ?_ hm) hmv.le
      intro j
      have hjL : 0 ≤ (j : ℝ) * L := mul_nonneg (Nat.cast_nonneg j) hL.le
      have hdist : (j : ℝ) * L ≤ |((j : ℝ) + 1) * L - b| := by
        rw [abs_of_nonneg (by nlinarith)]
        nlinarith
      exact gaussianPrimePowerScalar_le_uniform_geometric hN hx j j hdist
    nlinarith

theorem gaussianPrimeIdealRow_tsum_le_uniform (K : Type*) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) {x : ℝ} (hx : 0 < x) :
    (∑' j : ℕ, gaussianPrimeIdealPowerTerm K x (P, j)) ≤
      gaussianUniformRowConstant * Real.log (P.asIdeal.absNorm : ℝ) := by
  change (∑' j : ℕ, Real.log (P.asIdeal.absNorm : ℝ) *
    artinGaussianWeight ((P.asIdeal.absNorm : ℝ) ^ (j + 1) / x)) ≤ _
  have hn : 2 ≤ P.asIdeal.absNorm := NumberField.HeightOneSpectrum.one_lt_absNorm P
  have hN : (2 : ℝ) ≤ P.asIdeal.absNorm := by exact_mod_cast hn
  exact gaussianPrimePowerScalar_tsum_le_uniform hN hx

theorem gaussianRemovedBadPrimesTrace_le_uniform (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : n ≠ 0) {x : ℝ} (hx : 0 < x) :
    gaussianRemovedPrimeIdealTrace K (numberFieldBadPrimes K n hn) x ≤
      gaussianUniformRowConstant * Module.finrank ℚ K * Real.log n := by
  calc
    _ ≤ ∑ P ∈ numberFieldBadPrimes K n hn,
        gaussianUniformRowConstant * Real.log (P.asIdeal.absNorm : ℝ) :=
      Finset.sum_le_sum (fun P _ => gaussianPrimeIdealRow_tsum_le_uniform K P hx)
    _ = gaussianUniformRowConstant *
        ∑ P ∈ numberFieldBadPrimes K n hn, Real.log (P.asIdeal.absNorm : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ gaussianUniformRowConstant * ((Module.finrank ℚ K : ℝ) * Real.log n) :=
      mul_le_mul_of_nonneg_left (numberFieldBadPrimes_sum_log_norm_le K n hn)
        gaussianUniformRowConstant_pos.le
    _ = _ := by ring

end
end SimultaneousPrimitiveRoots
