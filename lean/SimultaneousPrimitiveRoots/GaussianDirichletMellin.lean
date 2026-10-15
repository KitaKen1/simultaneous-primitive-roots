module

public import SimultaneousPrimitiveRoots.NumberFieldPrimePowerDirichlet
public import SimultaneousPrimitiveRoots.GaussianPrimeIdealPowers
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain MeasureTheory
noncomputable section
open Classical

/-- The actual Gaussian trace after deleting the finite set of prime ideals S. -/
def gaussianDeletedPrimeIdealPowerTerm (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : ℝ)
    (pe : HeightOneSpectrum (𝓞 K) × ℕ) : ℝ :=
  if pe.1 ∈ S then 0 else gaussianPrimeIdealPowerTerm K x pe

def gaussianDeletedPrimeIdealTrace (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : ℝ) : ℝ :=
  ∑' pe, gaussianDeletedPrimeIdealPowerTerm K S x pe

def gaussianDirichletVerticalKernel (x σ y : ℝ) : ℂ :=
  ((1 / x : ℝ) : ℂ) ^ (-((σ : ℂ) + y * Complex.I)) *
    artinGaussianMellin ((σ : ℂ) + y * Complex.I)

theorem gaussianDirichletVerticalKernel_integrable {x : ℝ} (hx : 0 < x) (σ : ℝ) :
    Integrable (gaussianDirichletVerticalKernel x σ) :=
  artinGaussianMellin_inverse_integrable σ (one_div_pos.mpr hx)

theorem numberFieldDeletedPrimePowerTerm_vertical_norm (K : Type*) [Field K]
    [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (σ y : ℝ)
    (pe : HeightOneSpectrum (𝓞 K) × ℕ) :
    ‖numberFieldDeletedPrimePowerTerm K S ((σ : ℂ) + y * Complex.I) pe‖ =
      ‖numberFieldDeletedPrimePowerTerm K S (σ : ℂ) pe‖ := by
  simp only [numberFieldDeletedPrimePowerTerm_eq_normPower]
  split_ifs
  · rfl
  · have hn : 0 < pe.1.asIdeal.absNorm :=
      Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm pe.1)
    rw [norm_div, norm_div, ← Nat.cast_pow,
      Complex.norm_natCast_cpow_of_pos (pow_pos hn _),
      Complex.norm_natCast_cpow_of_pos (pow_pos hn _)]
    simp

private theorem scaledGaussianKernel {b x : ℝ} (hb : 0 < b) (hx : 0 < x) (s : ℂ) :
    ((1 / x : ℝ) : ℂ) ^ (-s) * artinGaussianMellin s / (b : ℂ) ^ s =
      ((b / x : ℝ) : ℂ) ^ (-s) * artinGaussianMellin s := by
  push_cast
  rw [Complex.div_cpow_ofReal_nonneg hb.le hx.le, one_div,
    Complex.inv_cpow_ofReal_nonneg hx.le, Complex.cpow_neg, Complex.cpow_neg]
  simp only [inv_inv, div_eq_mul_inv]
  ring

theorem gaussianDeletedPrimePowerKernel_eq (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {x : ℝ} (hx : 0 < x) (σ y : ℝ)
    (pe : HeightOneSpectrum (𝓞 K) × ℕ) :
    gaussianDirichletVerticalKernel x σ y *
      numberFieldDeletedPrimePowerTerm K S ((σ : ℂ) + y * Complex.I) pe =
    if pe.1 ∈ S then 0 else
      Complex.log (pe.1.asIdeal.absNorm : ℂ) *
        (((pe.1.asIdeal.absNorm : ℝ) ^ (pe.2 + 1) / x : ℝ) : ℂ) ^
          (-((σ : ℂ) + y * Complex.I)) *
        artinGaussianMellin ((σ : ℂ) + y * Complex.I) := by
  rw [numberFieldDeletedPrimePowerTerm_eq_normPower]
  split_ifs
  · simp
  · have hn : 0 < (pe.1.asIdeal.absNorm : ℝ) := by
      exact_mod_cast Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm pe.1)
    have h := scaledGaussianKernel (pow_pos hn (pe.2 + 1)) hx
      ((σ : ℂ) + y * Complex.I)
    push_cast at h
    unfold gaussianDirichletVerticalKernel
    push_cast
    linear_combination Complex.log (pe.1.asIdeal.absNorm : ℂ) * h

theorem gaussianDeletedPrimePowerKernel_integrable (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {x : ℝ} (hx : 0 < x) (σ : ℝ)
    (pe : HeightOneSpectrum (𝓞 K) × ℕ) :
    Integrable (fun y : ℝ => gaussianDirichletVerticalKernel x σ y *
      numberFieldDeletedPrimePowerTerm K S ((σ : ℂ) + y * Complex.I) pe) := by
  simp_rw [gaussianDeletedPrimePowerKernel_eq K S hx]
  by_cases hp : pe.1 ∈ S
  · simp [hp]
  · simp only [hp, ↓reduceIte, mul_assoc]
    have hn : 0 < (pe.1.asIdeal.absNorm : ℝ) := by
      exact_mod_cast Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm pe.1)
    exact (artinGaussianMellin_inverse_integrable σ (div_pos (pow_pos hn _) hx)).const_mul _

theorem gaussianDeletedPrimePowerKernel_integral (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {x : ℝ} (hx : 0 < x) (σ : ℝ)
    (pe : HeightOneSpectrum (𝓞 K) × ℕ) :
    (∫ y : ℝ, gaussianDirichletVerticalKernel x σ y *
      numberFieldDeletedPrimePowerTerm K S ((σ : ℂ) + y * Complex.I) pe) =
        ((2 * Real.pi * gaussianDeletedPrimeIdealPowerTerm K S x pe : ℝ) : ℂ) := by
  simp_rw [gaussianDeletedPrimePowerKernel_eq K S hx]
  by_cases hp : pe.1 ∈ S
  · simp [hp, gaussianDeletedPrimeIdealPowerTerm]
  · have hn : 0 < (pe.1.asIdeal.absNorm : ℝ) := by
      exact_mod_cast Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm pe.1)
    simp only [hp, ↓reduceIte, mul_assoc]
    rw [integral_const_mul, artinGaussianMellin_inverse_integral σ
      (div_pos (pow_pos hn _) hx), ← Complex.ofReal_natCast,
      ← Complex.ofReal_log hn.le, gaussianDeletedPrimeIdealPowerTerm,
      if_neg hp, gaussianPrimeIdealPowerTerm]
    push_cast
    ring

theorem gaussianDeletedPrimePowerKernel_integral_norm_summable (K : Type*) [Field K]
    [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) {x σ : ℝ}
    (_hx : 0 < x) (hσ : 1 < σ) :
    Summable (fun pe : HeightOneSpectrum (𝓞 K) × ℕ =>
      ∫ y : ℝ, ‖gaussianDirichletVerticalKernel x σ y *
        numberFieldDeletedPrimePowerTerm K S ((σ : ℂ) + y * Complex.I) pe‖) := by
  have heq (pe : HeightOneSpectrum (𝓞 K) × ℕ) :
      (∫ y : ℝ, ‖gaussianDirichletVerticalKernel x σ y *
        numberFieldDeletedPrimePowerTerm K S ((σ : ℂ) + y * Complex.I) pe‖) =
      ‖numberFieldDeletedPrimePowerTerm K S (σ : ℂ) pe‖ *
        ∫ y : ℝ, ‖gaussianDirichletVerticalKernel x σ y‖ := by
    simp_rw [norm_mul, numberFieldDeletedPrimePowerTerm_vertical_norm K S σ,
      mul_comm (‖gaussianDirichletVerticalKernel x σ _‖), integral_const_mul]
  simp_rw [heq]
  exact (numberFieldDeletedPrimePowerTerm_summable K S (by simpa using hσ)).norm.mul_right _

theorem numberFieldPrimeIdealPowers_countable (K : Type*) [Field K] [NumberField K] :
    Countable (HeightOneSpectrum (𝓞 K) × ℕ) := by
  letI (pe : Nat.Primes × ℕ) :
      Fintype ((Ideal.span {(pe.1.1 : ℤ)}).primesOver (𝓞 K)) :=
    (Algebra.QuasiFinite.finite_primesOver _).fintype
  exact Countable.of_equiv _ (numberFieldPrimePowerSigmaEquiv K)

theorem gaussianDeletedPrimePowerSeries_integrable (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    Integrable (fun y : ℝ => gaussianDirichletVerticalKernel x σ y *
      numberFieldDeletedPrimePowerSeries K S ((σ : ℂ) + y * Complex.I)) := by
  letI := numberFieldPrimeIdealPowers_countable K
  have hm : AEStronglyMeasurable (fun y : ℝ => ∑' pe,
      gaussianDirichletVerticalKernel x σ y *
        numberFieldDeletedPrimePowerTerm K S ((σ : ℂ) + y * Complex.I) pe) :=
    (AEMeasurable.tsum (fun pe =>
      (gaussianDeletedPrimePowerKernel_integrable K S hx σ pe).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hint := (gaussianDirichletVerticalKernel_integrable hx σ).norm.mul_const
    (∑' pe, ‖numberFieldDeletedPrimePowerTerm K S (σ : ℂ) pe‖)
  have htotal : Integrable (fun y : ℝ => ∑' pe,
      gaussianDirichletVerticalKernel x σ y *
        numberFieldDeletedPrimePowerTerm K S ((σ : ℂ) + y * Complex.I) pe) := by
    apply hint.mono' hm
    apply Filter.Eventually.of_forall
    intro y
    have hs := (numberFieldDeletedPrimePowerTerm_summable K S
      (s := (σ : ℂ) + y * Complex.I) (by simpa using hσ)).mul_left
        (gaussianDirichletVerticalKernel x σ y)
    calc
      _ ≤ ∑' pe, ‖gaussianDirichletVerticalKernel x σ y *
          numberFieldDeletedPrimePowerTerm K S ((σ : ℂ) + y * Complex.I) pe‖ :=
        norm_tsum_le_tsum_norm hs.norm
      _ = _ := by
        simp_rw [norm_mul, numberFieldDeletedPrimePowerTerm_vertical_norm K S σ]
        rw [tsum_mul_left]
  simpa only [tsum_mul_left, numberFieldDeletedPrimePowerSeries] using htotal

/-- Absolute convergence justifies the exchange with the actual deleted
Dirichlet series. This is on Re(s)>1 and does not shift the contour. -/
theorem gaussianDeletedPrimePower_integral_tsum (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    (∫ y : ℝ, gaussianDirichletVerticalKernel x σ y *
      numberFieldDeletedPrimePowerSeries K S ((σ : ℂ) + y * Complex.I)) =
        ((2 * Real.pi * gaussianDeletedPrimeIdealTrace K S x : ℝ) : ℂ) := by
  letI := numberFieldPrimeIdealPowers_countable K
  have h := integral_tsum_of_summable_integral_norm
    (gaussianDeletedPrimePowerKernel_integrable K S hx σ)
    (gaussianDeletedPrimePowerKernel_integral_norm_summable K S hx hσ)
  simp_rw [gaussianDeletedPrimePowerKernel_integral K S hx σ] at h
  simpa only [gaussianDeletedPrimeIdealTrace, numberFieldDeletedPrimePowerSeries,
    Nat.cast_ofNat, Complex.ofReal_mul, tsum_mul_left, ← Complex.ofReal_tsum] using h.symm

/-- The deleted Gaussian coefficients are absolutely summable for any
number field, without a Galois hypothesis. -/
theorem gaussianDeletedPrimeIdealPowerTerm_summable (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {x : ℝ} (hx : 0 < x) :
    Summable (gaussianDeletedPrimeIdealPowerTerm K S x) := by
  letI := numberFieldPrimeIdealPowers_countable K
  have h := (hasSum_integral_of_summable_integral_norm
    (gaussianDeletedPrimePowerKernel_integrable K S hx 2)
    (gaussianDeletedPrimePowerKernel_integral_norm_summable K S hx
      (by norm_num : (1 : ℝ) < 2))).summable
  simp_rw [gaussianDeletedPrimePowerKernel_integral K S hx 2] at h
  have hr := Complex.summable_ofReal.mp h
  exact (summable_mul_left_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
    Real.pi_ne_zero)).mp hr

theorem gaussianDeletedPrimeIdealPowerTerm_hasSum (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {x : ℝ} (hx : 0 < x) :
    HasSum (gaussianDeletedPrimeIdealPowerTerm K S x) (gaussianDeletedPrimeIdealTrace K S x) :=
  (gaussianDeletedPrimeIdealPowerTerm_summable K S hx).hasSum

theorem gaussianDeletedPrimeIdealTrace_mellinInv (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    mellinInv σ (fun s => artinGaussianMellin s * numberFieldDeletedPrimePowerSeries K S s)
      (1 / x) = (gaussianDeletedPrimeIdealTrace K S x : ℂ) := by
  rw [mellinInv]
  simp only [smul_eq_mul, Complex.real_smul]
  simp_rw [← mul_assoc]
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ y : ℝ, gaussianDirichletVerticalKernel x σ y *
      numberFieldDeletedPrimePowerSeries K S ((σ : ℂ) + y * Complex.I)) = _
  rw [gaussianDeletedPrimePower_integral_tsum K S hx hσ]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- The Gaussian integral contains the actual deleted-zeta logarithmic
derivative; no estimate for zeros or exceptional primes is assumed. -/
theorem gaussianDeletedZetaLogDerivative_integral (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    (∫ y : ℝ, gaussianDirichletVerticalKernel x σ y *
      (-logDeriv (numberFieldIncompleteZeta K S) ((σ : ℂ) + y * Complex.I))) =
        ((2 * Real.pi * gaussianDeletedPrimeIdealTrace K S x : ℝ) : ℂ) := by
  rw [← gaussianDeletedPrimePower_integral_tsum K S hx hσ]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    rw [numberFieldDeletedPrimePowerSeries_eq_neg_logDeriv K S (by simpa using hσ)])

theorem gaussianDeletedZetaLogDerivative_integrable (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    Integrable (fun y : ℝ => gaussianDirichletVerticalKernel x σ y *
      (-logDeriv (numberFieldIncompleteZeta K S) ((σ : ℂ) + y * Complex.I))) := by
  apply (gaussianDeletedPrimePowerSeries_integrable K S hx hσ).congr
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    rw [numberFieldDeletedPrimePowerSeries_eq_neg_logDeriv K S (by simpa using hσ)])

theorem gaussianDeletedPrimeIdealTrace_empty (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {x : ℝ} (hx : 0 < x) :
    gaussianDeletedPrimeIdealTrace K ∅ x = gaussianPrimePowerTrace K x := by
  simp only [gaussianDeletedPrimeIdealTrace, gaussianDeletedPrimeIdealPowerTerm,
    Finset.notMem_empty, ↓reduceIte]
  exact (gaussianPrimePowerTrace_eq_primeIdeal_tsum K hx).symm

end
end SimultaneousPrimitiveRoots
