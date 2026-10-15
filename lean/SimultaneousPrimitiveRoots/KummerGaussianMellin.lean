module

public import SimultaneousPrimitiveRoots.GaussianDirichletMellin
public import SimultaneousPrimitiveRoots.KummerPrimePowerDirichlet

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain MeasureTheory
noncomputable section

/-- The actual signed Gaussian trace. Neither this trace nor its
Dirichlet coefficients are assumed nonnegative. -/
def primeKummerGaussianSignedTrace (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (x : ℝ) : ℝ :=
  (gaussianDeletedPrimeIdealTrace (PrimeKummerField a q) (primeKummerTopBadPrimes a q) x -
    gaussianDeletedPrimeIdealTrace (CyclotomicField q ℚ) (primeKummerBaseBadPrimes a q) x) /
      ((q - 1 : ℕ) : ℝ)

def primeKummerGaussianSignedTerm (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (x : ℝ) :
    ((HeightOneSpectrum (𝓞 (PrimeKummerField a q)) × ℕ) ⊕
      (HeightOneSpectrum (𝓞 (CyclotomicField q ℚ)) × ℕ)) → ℝ :=
  Sum.elim
    (fun pe => gaussianDeletedPrimeIdealPowerTerm (PrimeKummerField a q)
      (primeKummerTopBadPrimes a q) x pe / ((q - 1 : ℕ) : ℝ))
    (fun pe => -gaussianDeletedPrimeIdealPowerTerm (CyclotomicField q ℚ)
      (primeKummerBaseBadPrimes a q) x pe / ((q - 1 : ℕ) : ℝ))

theorem primeKummerGaussianSignedTerm_hasSum (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {x : ℝ} (hx : 0 < x) :
    HasSum (primeKummerGaussianSignedTerm a q x) (primeKummerGaussianSignedTrace a q x) := by
  have hK := (gaussianDeletedPrimeIdealPowerTerm_hasSum (PrimeKummerField a q)
    (primeKummerTopBadPrimes a q) hx).div_const ((q - 1 : ℕ) : ℝ)
  have hE := (gaussianDeletedPrimeIdealPowerTerm_hasSum (CyclotomicField q ℚ)
    (primeKummerBaseBadPrimes a q) hx).neg.div_const ((q - 1 : ℕ) : ℝ)
  have hsum : HasSum (primeKummerGaussianSignedTerm a q x)
      (gaussianDeletedPrimeIdealTrace (PrimeKummerField a q) (primeKummerTopBadPrimes a q) x /
        ((q - 1 : ℕ) : ℝ) +
      -gaussianDeletedPrimeIdealTrace (CyclotomicField q ℚ) (primeKummerBaseBadPrimes a q) x /
        ((q - 1 : ℕ) : ℝ)) := HasSum.sum hK hE
  convert hsum using 1
  rw [primeKummerGaussianSignedTrace]
  ring

theorem primeKummerGaussianSignedTerm_summable (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {x : ℝ} (hx : 0 < x) :
    Summable (primeKummerGaussianSignedTerm a q x) :=
  (primeKummerGaussianSignedTerm_hasSum a q hx).summable

private theorem primeKummerGaussian_integrand_eq (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {σ : ℝ} (hσ : 1 < σ) (x y : ℝ) :
    gaussianDirichletVerticalKernel x σ y *
      primeKummerSignedLogDerivative a q ((σ : ℂ) + y * Complex.I) =
    (gaussianDirichletVerticalKernel x σ y *
        numberFieldDeletedPrimePowerSeries (PrimeKummerField a q) (primeKummerTopBadPrimes a q)
          ((σ : ℂ) + y * Complex.I) -
      gaussianDirichletVerticalKernel x σ y *
        numberFieldDeletedPrimePowerSeries (CyclotomicField q ℚ) (primeKummerBaseBadPrimes a q)
          ((σ : ℂ) + y * Complex.I)) / ((q - 1 : ℕ) : ℂ) := by
  rw [primeKummerSignedLogDerivative_eq_primePowerSeries a q (by simpa using hσ)]
  ring

theorem primeKummerGaussianSignedLogDerivative_integrable (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    Integrable (fun y : ℝ => gaussianDirichletVerticalKernel x σ y *
      primeKummerSignedLogDerivative a q ((σ : ℂ) + y * Complex.I)) := by
  simp_rw [primeKummerGaussian_integrand_eq a q hσ]
  exact ((gaussianDeletedPrimePowerSeries_integrable (PrimeKummerField a q)
    (primeKummerTopBadPrimes a q) hx hσ).sub
      (gaussianDeletedPrimePowerSeries_integrable (CyclotomicField q ℚ)
        (primeKummerBaseBadPrimes a q) hx hσ)).div_const _

/-- The actual common-factor logarithmic derivative has the exact
Gaussian integral representation on every vertical line Re(s)>1. -/
theorem primeKummerGaussianSignedLogDerivative_integral (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    (∫ y : ℝ, gaussianDirichletVerticalKernel x σ y *
      primeKummerSignedLogDerivative a q ((σ : ℂ) + y * Complex.I)) =
        ((2 * Real.pi * primeKummerGaussianSignedTrace a q x : ℝ) : ℂ) := by
  simp_rw [primeKummerGaussian_integrand_eq a q hσ]
  rw [integral_div, integral_sub
    (gaussianDeletedPrimePowerSeries_integrable (PrimeKummerField a q)
      (primeKummerTopBadPrimes a q) hx hσ)
    (gaussianDeletedPrimePowerSeries_integrable (CyclotomicField q ℚ)
      (primeKummerBaseBadPrimes a q) hx hσ),
    gaussianDeletedPrimePower_integral_tsum _ _ hx hσ,
    gaussianDeletedPrimePower_integral_tsum _ _ hx hσ, primeKummerGaussianSignedTrace]
  push_cast
  ring

theorem primeKummerGaussianSignedTrace_mellinInv (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    mellinInv σ (fun s => artinGaussianMellin s * primeKummerSignedLogDerivative a q s)
      (1 / x) = (primeKummerGaussianSignedTrace a q x : ℂ) := by
  rw [mellinInv]
  simp only [smul_eq_mul, Complex.real_smul]
  simp_rw [← mul_assoc]
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ y : ℝ, gaussianDirichletVerticalKernel x σ y *
      primeKummerSignedLogDerivative a q ((σ : ℂ) + y * Complex.I)) = _
  rw [primeKummerGaussianSignedLogDerivative_integral a q hx hσ]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

end
end SimultaneousPrimitiveRoots
