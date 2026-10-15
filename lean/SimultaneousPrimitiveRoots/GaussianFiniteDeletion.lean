module

public import SimultaneousPrimitiveRoots.GaussianHigherPrimePowers
public import SimultaneousPrimitiveRoots.GaussianDirichletMellin
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.HigherPrimePowers

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain Filter Asymptotics
open scoped Topology
noncomputable section
open Classical

/-- A constant independent of the prime ideal and the number field. -/
def gaussianFiniteDeletionConstant (r : ℝ) : ℝ :=
  Real.exp ((Real.log 2) ^ 2 + r ^ 2 / 4) * r⁻¹ * (1 - (2 : ℝ) ^ (-r))⁻¹

theorem gaussianFiniteDeletionConstant_pos {r : ℝ} (hr : 0 < r) :
    0 < gaussianFiniteDeletionConstant r := by
  have hratio : (2 : ℝ) ^ (-r) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hr)
  have hd : 0 < 1 - (2 : ℝ) ^ (-r) := sub_pos.mpr hratio
  unfold gaussianFiniteDeletionConstant
  positivity

theorem gaussianPrimePowerScalar_le_geometric {N x r : ℝ}
    (hN : 2 ≤ N) (hx : 0 < x) (hr : 0 < r) (j : ℕ) :
    Real.log N * artinGaussianWeight (N ^ (j + 1) / x) ≤
      (Real.exp ((Real.log 2) ^ 2 + r ^ 2 / 4) * r⁻¹ * x ^ r) *
        ((2 : ℝ) ^ (-r)) ^ j := by
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hratio : N ^ (-r) ≤ (2 : ℝ) ^ (-r) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hN (by linarith)
  have hlogratio : Real.log N * N ^ (-r) ≤ r⁻¹ := by
    have h := mul_le_mul_of_nonneg_right (Real.log_le_rpow_div hN0.le hr)
      (Real.rpow_nonneg hN0.le (-r))
    rw [div_eq_mul_inv, mul_assoc, mul_comm r⁻¹, ← mul_assoc,
      ← Real.rpow_add hN0, add_neg_cancel, Real.rpow_zero, one_mul] at h
    exact h
  have hp : (N ^ (-r)) ^ j ≤ ((2 : ℝ) ^ (-r)) ^ j :=
    pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) hratio j
  calc
    _ ≤ Real.log N * (Real.exp ((Real.log 2) ^ 2 + r ^ 2 / 4) *
        x ^ r * (N ^ (-r)) ^ (j + 1)) :=
      mul_le_mul_of_nonneg_left (artinGaussianWeight_natPower_le_fractional hN0 hx r _) hlog
    _ = (Real.exp ((Real.log 2) ^ 2 + r ^ 2 / 4) * x ^ r) *
        ((Real.log N * N ^ (-r)) * (N ^ (-r)) ^ j) := by rw [pow_succ]; ring
    _ ≤ (Real.exp ((Real.log 2) ^ 2 + r ^ 2 / 4) * x ^ r) *
        (r⁻¹ * ((2 : ℝ) ^ (-r)) ^ j) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hlogratio hp (by positivity) (by positivity)
    _ = _ := by ring

theorem gaussianPrimePowerScalar_summable {N x r : ℝ}
    (hN : 2 ≤ N) (hx : 0 < x) (hr : 0 < r) :
    Summable (fun j : ℕ => Real.log N * artinGaussianWeight (N ^ (j + 1) / x)) := by
  have hratio : (2 : ℝ) ^ (-r) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hr)
  apply ((summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _) hratio).mul_left
    (Real.exp ((Real.log 2) ^ 2 + r ^ 2 / 4) * r⁻¹ * x ^ r)).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (Real.log_nonneg (by linarith : 1 ≤ N)) (artinGaussianWeight_pos _).le)]
  exact gaussianPrimePowerScalar_le_geometric hN hx hr j

theorem gaussianPrimePowerScalar_tsum_le {N x r : ℝ}
    (hN : 2 ≤ N) (hx : 0 < x) (hr : 0 < r) :
    (∑' j : ℕ, Real.log N * artinGaussianWeight (N ^ (j + 1) / x)) ≤
      gaussianFiniteDeletionConstant r * x ^ r := by
  have hratio : (2 : ℝ) ^ (-r) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hr)
  have hg := summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) (-r)) hratio
  have h := (gaussianPrimePowerScalar_summable hN hx hr).tsum_le_tsum
    (gaussianPrimePowerScalar_le_geometric hN hx hr)
    (hg.mul_left (Real.exp ((Real.log 2) ^ 2 + r ^ 2 / 4) * r⁻¹ * x ^ r))
  rw [hg.tsum_mul_left, tsum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _) hratio] at h
  unfold gaussianFiniteDeletionConstant
  convert h using 1 <;> first | rfl | ring

theorem gaussianPrimeIdealRow_summable (K : Type*) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) {x : ℝ} (hx : 0 < x) :
    Summable (fun j : ℕ => gaussianPrimeIdealPowerTerm K x (P, j)) := by
  change Summable (fun j : ℕ => Real.log (P.asIdeal.absNorm : ℝ) *
    artinGaussianWeight ((P.asIdeal.absNorm : ℝ) ^ (j + 1) / x))
  have hn : 2 ≤ P.asIdeal.absNorm := NumberField.HeightOneSpectrum.one_lt_absNorm P
  have hN : (2 : ℝ) ≤ P.asIdeal.absNorm := by
    exact_mod_cast hn
  exact gaussianPrimePowerScalar_summable (N := (P.asIdeal.absNorm : ℝ))
    (r := 1) hN hx (by norm_num : (0 : ℝ) < 1)

theorem gaussianPrimeIdealRow_tsum_le (K : Type*) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) {x r : ℝ} (hx : 0 < x) (hr : 0 < r) :
    (∑' j : ℕ, gaussianPrimeIdealPowerTerm K x (P, j)) ≤
      gaussianFiniteDeletionConstant r * x ^ r := by
  change (∑' j : ℕ, Real.log (P.asIdeal.absNorm : ℝ) *
    artinGaussianWeight ((P.asIdeal.absNorm : ℝ) ^ (j + 1) / x)) ≤ _
  have hn : 2 ≤ P.asIdeal.absNorm := NumberField.HeightOneSpectrum.one_lt_absNorm P
  have hN : (2 : ℝ) ≤ P.asIdeal.absNorm := by
    exact_mod_cast hn
  exact gaussianPrimePowerScalar_tsum_le (N := (P.asIdeal.absNorm : ℝ)) hN hx hr

/-- The contribution of the finitely many deleted Euler factors, including all powers. -/
def gaussianRemovedPrimeIdealTrace (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : ℝ) : ℝ :=
  ∑ P ∈ S, ∑' j : ℕ, gaussianPrimeIdealPowerTerm K x (P, j)

theorem gaussianRemovedPrimeIdealTrace_nonneg (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    0 ≤ gaussianRemovedPrimeIdealTrace K S x :=
  Finset.sum_nonneg fun P _ => tsum_nonneg fun j => gaussianPrimeIdealPowerTerm_nonneg K x (P, j)

theorem gaussianRemovedPrimeIdealTrace_le_card (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {x r : ℝ} (hx : 0 < x) (hr : 0 < r) :
    gaussianRemovedPrimeIdealTrace K S x ≤
      S.card * gaussianFiniteDeletionConstant r * x ^ r := by
  have h := Finset.sum_le_sum (fun P (_ : P ∈ S) => gaussianPrimeIdealRow_tsum_le K P hx hr)
  simpa only [gaussianRemovedPrimeIdealTrace, Finset.sum_const, nsmul_eq_mul, mul_assoc] using h

/-- Restoring the finite Euler deletion is an exact equality of the actual convergent sums. -/
theorem gaussianPrimePowerTrace_eq_deleted_add_removed (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] (S : Finset (HeightOneSpectrum (𝓞 K))) {x : ℝ} (hx : 0 < x) :
    gaussianPrimePowerTrace K x = gaussianDeletedPrimeIdealTrace K S x +
      gaussianRemovedPrimeIdealTrace K S x := by
  let f : HeightOneSpectrum (𝓞 K) → ℝ := fun P => ∑' j : ℕ, gaussianPrimeIdealPowerTerm K x (P, j)
  have hs := gaussianPrimeIdealPowerTerm_summable K hx
  have hf : Summable f := hs.prod
  have hfull : gaussianPrimePowerTrace K x = ∑' P, f P := by
    rw [gaussianPrimePowerTrace_eq_primeIdeal_tsum K hx, hs.tsum_prod]
  have hdel : gaussianDeletedPrimeIdealTrace K S x = ∑' P : {P // P ∉ S}, f P.val := by
    rw [gaussianDeletedPrimeIdealTrace,
      (gaussianDeletedPrimeIdealPowerTerm_summable K S hx).tsum_prod]
    change (∑' P : HeightOneSpectrum (𝓞 K), ∑' j : ℕ,
      gaussianDeletedPrimeIdealPowerTerm K S x (P, j)) =
        ∑' P : ↥{P : HeightOneSpectrum (𝓞 K) | P ∉ S}, f P.val
    rw [tsum_subtype]
    apply tsum_congr
    intro P
    by_cases hP : P ∈ S <;> simp [gaussianDeletedPrimeIdealPowerTerm, hP, f, Set.indicator]
  rw [hfull, hdel]
  exact (hf.sum_add_tsum_subtype_compl S).symm.trans (add_comm _ _)

theorem gaussianDeletedPrimeIdealTrace_le_full (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] (S : Finset (HeightOneSpectrum (𝓞 K))) {x : ℝ} (hx : 0 < x) :
    gaussianDeletedPrimeIdealTrace K S x ≤ gaussianPrimePowerTrace K x := by
  rw [gaussianPrimePowerTrace_eq_deleted_add_removed K S hx]
  exact le_add_of_nonneg_right (gaussianRemovedPrimeIdealTrace_nonneg K S x)

end
end SimultaneousPrimitiveRoots
