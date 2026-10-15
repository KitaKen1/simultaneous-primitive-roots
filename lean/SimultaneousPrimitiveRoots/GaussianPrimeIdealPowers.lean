module

public import SimultaneousPrimitiveRoots.PrimeIdealReindexing
public import SimultaneousPrimitiveRoots.GaussianPrimePowers
public import SimultaneousPrimitiveRoots.GaussianMellinInversion

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section
open Classical

/-- The actual prime-ideal/exponent term, with coefficient log NP. -/
def gaussianPrimeIdealPowerTerm (K : Type*) [Field K] [NumberField K]
    (x : ℝ) (pe : HeightOneSpectrum (𝓞 K) × ℕ) : ℝ :=
  Real.log (pe.1.asIdeal.absNorm : ℝ) *
    artinGaussianWeight ((pe.1.asIdeal.absNorm : ℝ) ^ (pe.2 + 1) / x)

theorem gaussianPrimeIdealPowerTerm_nonneg (K : Type*) [Field K] [NumberField K]
    (x : ℝ) (pe : HeightOneSpectrum (𝓞 K) × ℕ) :
    0 ≤ gaussianPrimeIdealPowerTerm K x pe :=
  mul_nonneg (Real.log_natCast_nonneg _) (artinGaussianWeight_pos _).le

/-- Grouping the finite fiber above p gives the already-defined rational
prime row, including the ramified primes. -/
theorem gaussianPrimePowerFiber_tsum (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] (x : ℝ) (p : Nat.Primes) (j : ℕ) :
    (∑' Q : (Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 K),
      Real.log (Q.1.absNorm : ℝ) * artinGaussianWeight ((Q.1.absNorm : ℝ) ^ (j + 1) / x)) =
        gaussianPrimePowerTerm K x p.1 j := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  have hterm (Q : (Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 K)) :
      Real.log (Q.1.absNorm : ℝ) * artinGaussianWeight ((Q.1.absNorm : ℝ) ^ (j + 1) / x) =
        (rationalPrimeResidueDegree K p.1 : ℝ) * Real.log p.1 *
          artinGaussianWeight ((p.1 : ℝ) ^ ((j + 1) * rationalPrimeResidueDegree K p.1) / x) := by
    rw [galois_prime_absNorm_eq_power (p := p.1) Q.1, Nat.cast_pow,
      Real.log_pow, ← pow_mul, Nat.mul_comm (rationalPrimeResidueDegree K p.1) (j + 1)]
  simp_rw [hterm]
  rw [tsum_const, Nat.card_coe_set_eq, nsmul_eq_mul, gaussianPrimePowerTerm,
    if_pos p.2, rationalPrimeIdealCount]
  ring

theorem gaussianPrimePowerPrimePair_summable (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {x : ℝ} (hx : 0 < x) :
    Summable (fun pe : Nat.Primes × ℕ => gaussianPrimePowerTerm K x pe.1.1 pe.2) := by
  apply (gaussianPrimePowerPair_summable K hx).comp_injective
    (i := fun pe : Nat.Primes × ℕ => (pe.1.1, pe.2))
  intro a b h
  exact Prod.ext (Subtype.ext (congrArg (fun v : ℕ × ℕ => v.1) h))
    (congrArg (fun v : ℕ × ℕ => v.2) h)

private theorem gaussianPrimePowerSigma_summable (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {x : ℝ} (hx : 0 < x) :
    Summable (fun v : Σ pe : Nat.Primes × ℕ, (Ideal.span {(pe.1.1 : ℤ)}).primesOver (𝓞 K) =>
      Real.log (v.2.1.absNorm : ℝ) *
        artinGaussianWeight ((v.2.1.absNorm : ℝ) ^ (v.1.2 + 1) / x)) := by
  apply (summable_sigma_of_nonneg (fun v =>
    mul_nonneg (Real.log_natCast_nonneg _) (artinGaussianWeight_pos _).le)).mpr
  constructor
  · intro pe
    letI : Fintype ((Ideal.span {(pe.1.1 : ℤ)}).primesOver (𝓞 K)) :=
      (Algebra.QuasiFinite.finite_primesOver _).fintype
    exact (hasSum_fintype _).summable
  · simpa only [gaussianPrimePowerFiber_tsum] using gaussianPrimePowerPrimePair_summable K hx

theorem gaussianPrimeIdealPowerTerm_summable (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {x : ℝ} (hx : 0 < x) :
    Summable (gaussianPrimeIdealPowerTerm K x) := by
  apply (numberFieldPrimePowerSigmaEquiv K).summable_iff.mp
  simpa only [Function.comp_def, gaussianPrimeIdealPowerTerm,
    numberFieldPrimePowerSigmaEquiv_asIdeal, numberFieldPrimePowerSigmaEquiv_exponent] using
      gaussianPrimePowerSigma_summable K hx

/-- The actual all-prime-ideal series is the existing full Gaussian trace;
no Hecke identity or analytic counting estimate is used. -/
theorem gaussianPrimePowerTrace_eq_primeIdeal_tsum (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {x : ℝ} (hx : 0 < x) :
    gaussianPrimePowerTrace K x = ∑' pe, gaussianPrimeIdealPowerTerm K x pe := by
  have hprime : gaussianPrimePowerTrace K x =
      ∑' p : Nat.Primes, ∑' j : ℕ, gaussianPrimePowerTerm K x p.1 j := by
    symm
    change (∑' p : {p : ℕ // p.Prime}, ∑' j : ℕ, gaussianPrimePowerTerm K x p.1 j) =
      ∑' p : ℕ, ∑' j : ℕ, gaussianPrimePowerTerm K x p j
    apply tsum_subtype_eq_of_support_subset
      (f := fun p : ℕ => ∑' j : ℕ, gaussianPrimePowerTerm K x p j)
      (s := {p : ℕ | p.Prime})
    intro p hp
    change p.Prime
    by_contra h
    apply hp
    simp [gaussianPrimePowerTerm, h]
  calc
    gaussianPrimePowerTrace K x = ∑' pe : Nat.Primes × ℕ,
        gaussianPrimePowerTerm K x pe.1.1 pe.2 :=
      hprime.trans (gaussianPrimePowerPrimePair_summable K hx).tsum_prod.symm
    _ = ∑' pe : Nat.Primes × ℕ,
        ∑' Q : (Ideal.span {(pe.1.1 : ℤ)}).primesOver (𝓞 K),
          Real.log (Q.1.absNorm : ℝ) *
            artinGaussianWeight ((Q.1.absNorm : ℝ) ^ (pe.2 + 1) / x) := by
      apply tsum_congr
      intro pe
      exact (gaussianPrimePowerFiber_tsum K x pe.1 pe.2).symm
    _ = ∑' v : Σ pe : Nat.Primes × ℕ, (Ideal.span {(pe.1.1 : ℤ)}).primesOver (𝓞 K),
        Real.log (v.2.1.absNorm : ℝ) *
          artinGaussianWeight ((v.2.1.absNorm : ℝ) ^ (v.1.2 + 1) / x) :=
      (gaussianPrimePowerSigma_summable K hx).tsum_sigma.symm
    _ = ∑' pe, gaussianPrimeIdealPowerTerm K x pe := by
      simpa only [gaussianPrimeIdealPowerTerm, numberFieldPrimePowerSigmaEquiv_asIdeal,
        numberFieldPrimePowerSigmaEquiv_exponent] using
          (numberFieldPrimePowerSigmaEquiv K).tsum_eq (gaussianPrimeIdealPowerTerm K x)

/-- Actual prime-power coefficients after the proved Gaussian Mellin
inversion. This is a term identity, not an integral/sum exchange. -/
theorem gaussianPrimeIdealPowerTerm_eq_mellinInv (K : Type*) [Field K] [NumberField K]
    (σ : ℝ) {x : ℝ} (hx : 0 < x) (pe : HeightOneSpectrum (𝓞 K) × ℕ) :
    gaussianPrimeIdealPowerTerm K x pe = Real.log (pe.1.asIdeal.absNorm : ℝ) *
      (mellinInv σ artinGaussianMellin ((pe.1.asIdeal.absNorm : ℝ) ^ (pe.2 + 1) / x)).re := by
  have hnorm : 0 < (pe.1.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm pe.1))
  rw [artinGaussianMellin_mellinInv σ (div_pos (pow_pos hnorm _) hx), Complex.ofReal_re]
  rfl

theorem gaussianPrimePowerTrace_eq_primeIdeal_mellinInv (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    gaussianPrimePowerTrace K x = ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
      Real.log (pe.1.asIdeal.absNorm : ℝ) *
        (mellinInv σ artinGaussianMellin ((pe.1.asIdeal.absNorm : ℝ) ^ (pe.2 + 1) / x)).re := by
  rw [gaussianPrimePowerTrace_eq_primeIdeal_tsum K hx]
  apply tsum_congr
  exact gaussianPrimeIdealPowerTerm_eq_mellinInv K σ hx

end
end SimultaneousPrimitiveRoots
