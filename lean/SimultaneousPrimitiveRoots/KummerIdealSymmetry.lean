module

public import SimultaneousPrimitiveRoots.NumberFieldIdealSymmetry
public import SimultaneousPrimitiveRoots.KummerCharacterConjugacy

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section

/-- The base automorphism is obtained by actual normal restriction,
not by choosing an unrelated permutation of prime ideals. -/
def primeKummerBaseAutomorphism (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (τ : Gal(PrimeKummerField a q/ℚ)) : Gal(CyclotomicField q ℚ/ℚ) := by
  let := prime_cyclotomic_normal q
  exact τ.restrictNormal (CyclotomicField q ℚ)

theorem primeKummerBaseAutomorphism_commutes (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (τ : Gal(PrimeKummerField a q/ℚ)) (z : CyclotomicField q ℚ) :
    τ (algebraMap (CyclotomicField q ℚ) (PrimeKummerField a q) z) =
      algebraMap (CyclotomicField q ℚ) (PrimeKummerField a q)
        (primeKummerBaseAutomorphism a q τ z) := by
  let := prime_cyclotomic_normal q
  exact (AlgEquiv.restrictNormal_commutes τ (CyclotomicField q ℚ) z).symm

theorem primeKummerBaseAutomorphism_integers_commutes (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (τ : Gal(PrimeKummerField a q/ℚ)) (z : 𝓞 (CyclotomicField q ℚ)) :
    RingOfIntegers.mapRingEquiv τ.toRingEquiv
      (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q)) z) =
      algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q))
        (RingOfIntegers.mapRingEquiv (primeKummerBaseAutomorphism a q τ).toRingEquiv z) := by
  apply RingOfIntegers.ext
  exact primeKummerBaseAutomorphism_commutes a q τ (z : CyclotomicField q ℚ)

/-- The prime above P is transported consistently with the transported
base prime, an algebraic prerequisite for Frobenius covariance. -/
theorem primeKummerIdeal_map_comap (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (τ : Gal(PrimeKummerField a q/ℚ)) (I : Ideal (𝓞 (PrimeKummerField a q))) :
    (I.map (RingOfIntegers.mapRingEquiv τ.toRingEquiv)).comap
      (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q))) =
      (I.comap (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q)))).map
        (RingOfIntegers.mapRingEquiv (primeKummerBaseAutomorphism a q τ).toRingEquiv) :=
  idealMap_comap_commuting _ _ _ (primeKummerBaseAutomorphism_integers_commutes a q τ) I

/-- The prime-ideal permutation of E attached to this same absolute
automorphism. It includes primes above a and q. -/
def primeKummerBasePrimeEquiv (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (τ : Gal(PrimeKummerField a q/ℚ)) :
    HeightOneSpectrum (𝓞 (CyclotomicField q ℚ)) ≃
      HeightOneSpectrum (𝓞 (CyclotomicField q ℚ)) :=
  numberFieldPrimeIdealEquiv (primeKummerBaseAutomorphism a q τ).toRingEquiv

theorem primeKummerBasePrimeEquiv_absNorm (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (τ : Gal(PrimeKummerField a q/ℚ)) (P : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ))) :
    (primeKummerBasePrimeEquiv a q τ P).asIdeal.absNorm = P.asIdeal.absNorm :=
  numberFieldPrimeIdealEquiv_absNorm (primeKummerBaseAutomorphism a q τ).toRingEquiv P

theorem primeKummerBasePrimeEquiv_natCast_mem (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (τ : Gal(PrimeKummerField a q/ℚ))
    (P : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ))) (n : ℕ) :
    (n : 𝓞 (CyclotomicField q ℚ)) ∈ (primeKummerBasePrimeEquiv a q τ P).asIdeal ↔
      (n : 𝓞 (CyclotomicField q ℚ)) ∈ P.asIdeal :=
  numberFieldPrimeIdealEquiv_natCast_mem (primeKummerBaseAutomorphism a q τ).toRingEquiv P n

/-- Character pullback and the norm-preserving base prime permutation
come from one and the same actual absolute field automorphism. -/
theorem primeKummer_nonprincipal_character_ideal_symmetry (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ ψ : PrimeKummerCharacter a q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    ∃ m : Fin q, m.val ≠ 0 ∧ ∃ τ : Gal(PrimeKummerField a q/ℚ),
      (∀ σ : Gal(PrimeKummerField a q/CyclotomicField q ℚ),
        τ * σ.restrictScalars ℚ * τ⁻¹ = (σ ^ m.val).restrictScalars ℚ) ∧
      (∀ σ : Gal(PrimeKummerField a q/CyclotomicField q ℚ), ψ σ = χ (σ ^ m.val)) ∧
      (∀ P : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ)),
        (primeKummerBasePrimeEquiv a q τ P).asIdeal.absNorm = P.asIdeal.absNorm) := by
  obtain ⟨m, hm, τ, hτ, hχψ⟩ := primeKummer_nonprincipal_character_conjugacy a q χ ψ hχ hψ
  exact ⟨m, hm, τ, hτ, hχψ, primeKummerBasePrimeEquiv_absNorm a q τ⟩

end
end SimultaneousPrimitiveRoots
