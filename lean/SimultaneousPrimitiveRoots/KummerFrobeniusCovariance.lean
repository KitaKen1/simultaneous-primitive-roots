module

public import SimultaneousPrimitiveRoots.KummerIdealSymmetry

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section

/-- Transport the defining power congruence across the actual integer-ring
automorphism. The statement includes both directions. -/
theorem numberField_powerCongruence_covariance {K : Type*} [Field K]
    (τ σ γ : K ≃+* K) (hcomm : ∀ z, τ (σ z) = γ (τ z))
    (I : Ideal (𝓞 K)) (n : ℕ) :
    (∀ z : 𝓞 K, RingOfIntegers.mapRingEquiv σ z - z ^ n ∈ I) ↔
      (∀ z : 𝓞 K, RingOfIntegers.mapRingEquiv γ z - z ^ n ∈
        I.map (RingOfIntegers.mapRingEquiv τ)) := by
  let τO := RingOfIntegers.mapRingEquiv τ
  let σO := RingOfIntegers.mapRingEquiv σ
  let γO := RingOfIntegers.mapRingEquiv γ
  have hO (z : 𝓞 K) : τO (σO z) = γO (τO z) := by
    apply RingOfIntegers.ext
    exact hcomm (z : K)
  change (∀ z, σO z - z ^ n ∈ I) ↔ (∀ z, γO z - z ^ n ∈ I.map τO)
  constructor
  · intro h z
    obtain ⟨y, rfl⟩ := τO.surjective z
    have hy := Ideal.mem_map_of_mem τO (h y)
    simpa only [map_sub, map_pow, hO] using hy
  · intro h z
    have hz := h (τO z)
    rw [← hO, ← map_pow, ← map_sub] at hz
    exact (Ideal.apply_mem_of_equiv_iff).mp hz

/-- The standard residue-power characterization of a relative Frobenius
element at this actual prime ideal. Existence and uniqueness at unramified
primes are separate goals; this definition supplies neither. -/
def primeKummerFrobeniusCondition (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (P : HeightOneSpectrum (𝓞 (PrimeKummerField a q)))
    (σ : Gal(PrimeKummerField a q/CyclotomicField q ℚ)) : Prop :=
  ∀ z : 𝓞 (PrimeKummerField a q),
    RingOfIntegers.mapRingEquiv σ.toRingEquiv z -
      z ^ (P.asIdeal.comap
        (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q)))).absNorm ∈ P.asIdeal

theorem primeKummerPrimeEquiv_contraction_absNorm (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (τ : Gal(PrimeKummerField a q/ℚ))
    (P : HeightOneSpectrum (𝓞 (PrimeKummerField a q))) :
    ((numberFieldPrimeIdealEquiv τ.toRingEquiv P).asIdeal.comap
      (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q)))).absNorm =
      (P.asIdeal.comap
        (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q)))).absNorm := by
  rw [numberFieldPrimeIdealEquiv_asIdeal, primeKummerIdeal_map_comap,
    numberFieldIdeal_map_absNorm]

/-- Actual Frobenius congruences are covariant under absolute conjugation,
with the transported actual prime and the correct base residue norm. -/
theorem primeKummerFrobeniusCondition_conjugation (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (τ : Gal(PrimeKummerField a q/ℚ))
    (σ γ : Gal(PrimeKummerField a q/CyclotomicField q ℚ))
    (hconj : τ * σ.restrictScalars ℚ * τ⁻¹ = γ.restrictScalars ℚ)
    (P : HeightOneSpectrum (𝓞 (PrimeKummerField a q))) :
    primeKummerFrobeniusCondition a q P σ ↔
      primeKummerFrobeniusCondition a q (numberFieldPrimeIdealEquiv τ.toRingEquiv P) γ := by
  have hsem : τ * σ.restrictScalars ℚ = γ.restrictScalars ℚ * τ := by
    calc
      τ * σ.restrictScalars ℚ = (τ * σ.restrictScalars ℚ * τ⁻¹) * τ := by
        simp only [mul_assoc, inv_mul_cancel, mul_one]
      _ = γ.restrictScalars ℚ * τ := by rw [hconj]
  have hcomm (z : PrimeKummerField a q) : τ (σ z) = γ (τ z) := by
    exact congrArg (fun f : Gal(PrimeKummerField a q/ℚ) => f z) hsem
  unfold primeKummerFrobeniusCondition
  rw [primeKummerPrimeEquiv_contraction_absNorm, numberFieldPrimeIdealEquiv_asIdeal]
  exact numberField_powerCongruence_covariance τ.toRingEquiv σ.toRingEquiv γ.toRingEquiv
    hcomm P.asIdeal _

/-- The same actual automorphism realizes character pullback, preserves
base prime norms, and transports every residue-power Frobenius condition.
This does not assert that a Frobenius element exists at every prime. -/
theorem primeKummer_nonprincipal_character_frobenius_symmetry (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ ψ : PrimeKummerCharacter a q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    ∃ m : Fin q, m.val ≠ 0 ∧ ∃ τ : Gal(PrimeKummerField a q/ℚ),
      (∀ σ : Gal(PrimeKummerField a q/CyclotomicField q ℚ), ψ σ = χ (σ ^ m.val)) ∧
      (∀ P : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ)),
        (primeKummerBasePrimeEquiv a q τ P).asIdeal.absNorm = P.asIdeal.absNorm) ∧
      (∀ P : HeightOneSpectrum (𝓞 (PrimeKummerField a q)),
        ∀ σ : Gal(PrimeKummerField a q/CyclotomicField q ℚ),
          primeKummerFrobeniusCondition a q P σ ↔
            primeKummerFrobeniusCondition a q
              (numberFieldPrimeIdealEquiv τ.toRingEquiv P) (σ ^ m.val)) := by
  obtain ⟨m, hm, τ, hτ, hχψ, hnorm⟩ :=
    primeKummer_nonprincipal_character_ideal_symmetry a q χ ψ hχ hψ
  exact ⟨m, hm, τ, hχψ, hnorm, fun P σ =>
    primeKummerFrobeniusCondition_conjugation a q τ σ (σ ^ m.val) (hτ σ) P⟩

end
end SimultaneousPrimitiveRoots
