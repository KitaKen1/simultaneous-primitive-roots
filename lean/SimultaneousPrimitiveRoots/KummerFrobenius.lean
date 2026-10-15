module

public import SimultaneousPrimitiveRoots.NumberFieldFrobenius
public import SimultaneousPrimitiveRoots.KummerFrobeniusCovariance
public import SimultaneousPrimitiveRoots.KummerAbsoluteDiscriminant

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
open scoped IsMulCommutative
noncomputable section

/-- An actual relative Frobenius lift, using the coherent existing choice.
It is uniquely determined at unramified primes. -/
def primeKummerFrobenius (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (P : HeightOneSpectrum (𝓞 (PrimeKummerField a q))) :
    Gal(PrimeKummerField a q/CyclotomicField q ℚ) := by
  let := primeKummer_relative_galois a q
  exact numberFieldFrobenius (E := CyclotomicField q ℚ) P

theorem primeKummerFrobenius_condition (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (P : HeightOneSpectrum (𝓞 (PrimeKummerField a q))) :
    primeKummerFrobeniusCondition a q P (primeKummerFrobenius a q P) := by
  let := primeKummer_relative_galois a q
  exact numberFieldFrobenius_condition (E := CyclotomicField q ℚ) P

theorem primeKummer_exists_frobenius (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (P : HeightOneSpectrum (𝓞 (PrimeKummerField a q))) :
    ∃ σ : Gal(PrimeKummerField a q/CyclotomicField q ℚ),
      primeKummerFrobeniusCondition a q P σ :=
  ⟨primeKummerFrobenius a q P, primeKummerFrobenius_condition a q P⟩

theorem primeKummer_frobenius_unique (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (P : HeightOneSpectrum (𝓞 (PrimeKummerField a q)))
    [Algebra.IsUnramifiedAt (𝓞 (CyclotomicField q ℚ)) P.asIdeal]
    (σ γ : Gal(PrimeKummerField a q/CyclotomicField q ℚ))
    (hσ : primeKummerFrobeniusCondition a q P σ)
    (hγ : primeKummerFrobeniusCondition a q P γ) : σ = γ := by
  let := primeKummer_relative_galois a q
  exact numberField_frobenius_unique P σ γ hσ hγ

/-- The already verified absolute discriminant bound supplies the local
relative nonramification needed for uniqueness, without a new inertia
calculation. -/
theorem primeKummer_relative_unramified_away {a p q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpq : ¬ p ∣ q)
    (P : HeightOneSpectrum (𝓞 (PrimeKummerField a q)))
    (hpP : (p : 𝓞 (PrimeKummerField a q)) ∈ P.asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 (CyclotomicField q ℚ)) P.asIdeal := by
  let : P.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    (Ideal.liesOver_span_iff P.isPrime.ne_top (Nat.prime_iff_prime_int.mp hp)).mpr hpP
  let : Algebra.IsUnramifiedAt ℤ P.asIdeal :=
    primeKummer_unramified_away hp hpa hpq P.asIdeal inferInstance inferInstance
  exact Algebra.IsUnramifiedAt.of_restrictScalars ℤ P.asIdeal

theorem primeKummer_exists_unique_frobenius_away {a p q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpq : ¬ p ∣ q)
    (P : HeightOneSpectrum (𝓞 (PrimeKummerField a q)))
    (hpP : (p : 𝓞 (PrimeKummerField a q)) ∈ P.asIdeal) :
    ∃! σ : Gal(PrimeKummerField a q/CyclotomicField q ℚ),
      primeKummerFrobeniusCondition a q P σ := by
  let := primeKummer_relative_unramified_away hp hpa hpq P hpP
  exact ⟨primeKummerFrobenius a q P, primeKummerFrobenius_condition a q P,
    fun σ hσ => primeKummer_frobenius_unique a q P σ _ hσ
      (primeKummerFrobenius_condition a q P)⟩

/-- In this actual abelian extension the coherent chosen Frobenius
is independent of the prime selected above a fixed base prime. -/
theorem primeKummerFrobenius_eq_of_contraction (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (P Q : HeightOneSpectrum (𝓞 (PrimeKummerField a q)))
    (hPQ : P.asIdeal.comap
        (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q))) =
      Q.asIdeal.comap
        (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q)))) :
    primeKummerFrobenius a q P = primeKummerFrobenius a q Q := by
  let := primeKummer_relative_isAbelianGalois a q
  exact isConj_iff_eq.mp (numberFieldFrobenius_isConj (E := CyclotomicField q ℚ) P Q hPQ)

/-- Conjugation transports the actual unique Frobenius value away from
prime divisors of a*q, rather than only transporting its predicate. -/
theorem primeKummerFrobenius_eq_of_conjugation_away {a p q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpq : ¬ p ∣ q)
    (P : HeightOneSpectrum (𝓞 (PrimeKummerField a q)))
    (hpP : (p : 𝓞 (PrimeKummerField a q)) ∈ P.asIdeal)
    (τ : Gal(PrimeKummerField a q/ℚ))
    (γ : Gal(PrimeKummerField a q/CyclotomicField q ℚ))
    (hconj : τ * (primeKummerFrobenius a q P).restrictScalars ℚ * τ⁻¹ =
      γ.restrictScalars ℚ) :
    primeKummerFrobenius a q (numberFieldPrimeIdealEquiv τ.toRingEquiv P) = γ := by
  have hpT : (p : 𝓞 (PrimeKummerField a q)) ∈
      (numberFieldPrimeIdealEquiv τ.toRingEquiv P).asIdeal :=
    (numberFieldPrimeIdealEquiv_natCast_mem τ.toRingEquiv P p).mpr hpP
  let := primeKummer_relative_unramified_away hp hpa hpq _ hpT
  exact primeKummer_frobenius_unique a q _ _ γ (primeKummerFrobenius_condition a q _)
    ((primeKummerFrobeniusCondition_conjugation a q τ _ γ hconj P).mp
      (primeKummerFrobenius_condition a q P))

/-- Actual nonprincipal character values at actual unramified Frobenius
are related by a single norm-preserving field-automorphism permutation. -/
theorem primeKummer_nonprincipal_character_frobenius_values (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ ψ : PrimeKummerCharacter a q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    ∃ τ : Gal(PrimeKummerField a q/ℚ),
      (∀ v : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ)),
        (primeKummerBasePrimeEquiv a q τ v).asIdeal.absNorm = v.asIdeal.absNorm) ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ a → ¬ p ∣ q →
        ∀ P : HeightOneSpectrum (𝓞 (PrimeKummerField a q)),
          (p : 𝓞 (PrimeKummerField a q)) ∈ P.asIdeal →
          ψ (primeKummerFrobenius a q P) =
            χ (primeKummerFrobenius a q (numberFieldPrimeIdealEquiv τ.toRingEquiv P))) := by
  obtain ⟨m, _, τ, hτ, hχψ⟩ := primeKummer_nonprincipal_character_conjugacy a q χ ψ hχ hψ
  refine ⟨τ, primeKummerBasePrimeEquiv_absNorm a q τ, ?_⟩
  intro p hp hpa hpq P hpP
  rw [primeKummerFrobenius_eq_of_conjugation_away hp hpa hpq P hpP τ _
    (hτ (primeKummerFrobenius a q P))]
  exact hχψ (primeKummerFrobenius a q P)

end
end SimultaneousPrimitiveRoots
