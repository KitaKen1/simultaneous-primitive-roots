module

public import SimultaneousPrimitiveRoots.KummerLogDerivative
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Deriv

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
open Classical

/-- The actual prime-power Dirichlet term after deleting S. The first
power is indexed by j=0, and the coefficient is log(NP), not log(NP^(j+1)). -/
def numberFieldDeletedPrimePowerTerm (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ)
    (pe : HeightOneSpectrum (𝓞 K) × ℕ) : ℂ :=
  if pe.1 ∈ S then 0 else
    Complex.log (pe.1.asIdeal.absNorm : ℂ) * (1 / (pe.1.asIdeal.absNorm : ℂ) ^ s) ^ (pe.2 + 1)

def numberFieldDeletedPrimePowerSeries (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ, numberFieldDeletedPrimePowerTerm K S s pe

private theorem deletedWeight_norm_le_one (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (I : (Ideal (𝓞 K))⁰) :
    ‖(TauCeti.MultiplicativeIdealWeight.ofBadPrimes (S : Set (HeightOneSpectrum (𝓞 K)))
      S.finite_toSet).toIdealArithmeticFunction I‖ ≤ 1 := by
  classical
  rw [TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_apply,
    TauCeti.MultiplicativeIdealWeight.ofBadPrimes_apply]
  split_ifs <;> simp

/-- The selected 0/1 ideal weight produces precisely the actual deleted terms. -/
theorem numberFieldDeletedPrimePowerTerm_eq_weight (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ)
    (pe : HeightOneSpectrum (𝓞 K) × ℕ) :
    numberFieldDeletedPrimePowerTerm K S s pe =
      Complex.log (pe.1.asIdeal.absNorm : ℂ) *
        ((TauCeti.MultiplicativeIdealWeight.ofBadPrimes
          (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet) pe.1.asIdeal /
            (pe.1.asIdeal.absNorm : ℂ) ^ s) ^ (pe.2 + 1) := by
  classical
  simp only [numberFieldDeletedPrimePowerTerm,
    TauCeti.MultiplicativeIdealWeight.ofBadPrimes_apply, Ideal.isPrimeTo_asIdeal_iff,
    Finset.mem_coe]
  split_ifs <;> simp_all

/-- Absolute convergence over prime ideals and exponents together. No
convergence of the literal series is claimed on Re(s)=1. -/
theorem numberFieldDeletedPrimePowerTerm_summable (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    Summable (numberFieldDeletedPrimePowerTerm K S s) := by
  let χ := TauCeti.MultiplicativeIdealWeight.ofBadPrimes
    (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet
  obtain ⟨y, hy, hys⟩ := exists_between hs
  have hconv : Summable (TauCeti.idealTerm K χ.toIdealArithmeticFunction (y : ℂ)) :=
    TauCeti.summable_idealTerm_of_bounded_of_one_lt_re (deletedWeight_norm_le_one K S)
      (by simpa using hy)
  have hmajor := χ.summable_log_absNorm_mul_norm_prime_pow
    (s := (y : ℂ)) (s' := (s.re : ℂ)) (by simpa using hys) hconv
  apply hmajor.of_norm_bounded
  intro pe
  rw [numberFieldDeletedPrimePowerTerm_eq_weight K S s pe]
  have h := χ.norm_log_mul_prime_pow_le pe.1 pe.2 (σ₀ := s.re) (z := s) le_rfl
  simpa only [norm_neg] using h

/-- The actual prime-power series equals the negative logarithmic
derivative of the actual deleted ideal-counting LSeries. -/
theorem numberFieldDeletedPrimePowerSeries_eq_neg_logDeriv (K : Type*) [Field K]
    [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    numberFieldDeletedPrimePowerSeries K S s = -logDeriv (numberFieldIncompleteZeta K S) s := by
  let χ := TauCeti.MultiplicativeIdealWeight.ofBadPrimes
    (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet
  have habs := TauCeti.idealAbscissaOfAbsConv_lt_re_of_bounded
    (deletedWeight_norm_le_one K S) hs
  have h := χ.logDeriv_LSeries_eq_tsum_prime_pow habs
  rw [tsum_neg] at h
  rw [numberFieldDeletedPrimePowerSeries]
  simp only [numberFieldDeletedPrimePowerTerm_eq_weight K S s]
  have hfun : numberFieldIncompleteZeta K S =
      LSeries (TauCeti.normCoeff K χ.toIdealArithmeticFunction) := by
    funext z
    rfl
  rw [hfun]
  simpa only [neg_neg, χ] using (congrArg Neg.neg h).symm

/-- The Dirichlet exponent is the actual norm of P^(j+1), with the
coefficient log NP unchanged. -/
theorem numberFieldDeletedPrimePowerTerm_eq_normPower (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ)
    (pe : HeightOneSpectrum (𝓞 K) × ℕ) :
    numberFieldDeletedPrimePowerTerm K S s pe =
      if pe.1 ∈ S then 0 else Complex.log (pe.1.asIdeal.absNorm : ℂ) /
        ((pe.1.asIdeal.absNorm : ℂ) ^ (pe.2 + 1)) ^ s := by
  unfold numberFieldDeletedPrimePowerTerm
  split_ifs
  · rfl
  · rw [div_pow, one_pow, ← Complex.cpow_nat_mul,
      Complex.natCast_cpow_natCast_mul, mul_one_div]

theorem numberFieldDeletedPrimePowerTerm_hasSum (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    HasSum (numberFieldDeletedPrimePowerTerm K S s)
      (-logDeriv (numberFieldIncompleteZeta K S) s) := by
  rw [← numberFieldDeletedPrimePowerSeries_eq_neg_logDeriv K S hs]
  exact (numberFieldDeletedPrimePowerTerm_summable K S hs).hasSum

end
end SimultaneousPrimitiveRoots
