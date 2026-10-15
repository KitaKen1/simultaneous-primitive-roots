module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.Frobenius

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section

variable {E K : Type*} [Field E] [Field K] [NumberField E] [NumberField K]
  [Algebra E K] [IsGalois E K]

omit [NumberField E] [NumberField K] [IsGalois E K] in
/-- The standard group action is the actual integer-ring restriction
used in the earlier congruence statements. -/
theorem numberFieldInteger_smul_eq (σ : Gal(K/E)) (z : 𝓞 K) :
    σ • z = RingOfIntegers.mapRingEquiv σ.toRingEquiv z := by
  apply RingOfIntegers.ext
  rfl

/-- The existing Frobenius predicate has precisely the contracted ideal
norm used in the Kummer congruence criterion. -/
theorem numberField_isArithFrobAt_iff (P : HeightOneSpectrum (𝓞 K)) (σ : Gal(K/E)) :
    IsArithFrobAt (𝓞 E) σ P.asIdeal ↔
      ∀ z : 𝓞 K, RingOfIntegers.mapRingEquiv σ.toRingEquiv z -
        z ^ (P.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K))).absNorm ∈ P.asIdeal := by
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  change (∀ z : 𝓞 K, (σ • z : 𝓞 K) -
    z ^ Nat.card (𝓞 E ⧸ P.asIdeal.under (𝓞 E)) ∈ P.asIdeal) ↔ _
  simp only [numberFieldInteger_smul_eq, Ideal.under_def]

/-- Frobenius exists at every actual nonzero prime, including ramified
ones. At ramified primes the chosen lift need not be unique. -/
theorem numberField_exists_frobenius (P : HeightOneSpectrum (𝓞 K)) :
    ∃ σ : Gal(K/E), ∀ z : 𝓞 K,
      RingOfIntegers.mapRingEquiv σ.toRingEquiv z -
        z ^ (P.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K))).absNorm ∈ P.asIdeal := by
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E) Gal(K/E) P.asIdeal
  exact ⟨σ, (numberField_isArithFrobAt_iff P σ).mp hσ⟩

/-- Reuse the coherent Mathlib choice: lifts above a single base prime
are conjugate, even when that prime ramifies. -/
def numberFieldFrobenius (P : HeightOneSpectrum (𝓞 K)) : Gal(K/E) :=
  arithFrobAt (𝓞 E) Gal(K/E) P.asIdeal

theorem numberFieldFrobenius_condition (P : HeightOneSpectrum (𝓞 K)) :
    ∀ z : 𝓞 K, RingOfIntegers.mapRingEquiv (numberFieldFrobenius (E := E) P).toRingEquiv z -
      z ^ (P.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K))).absNorm ∈ P.asIdeal :=
  (numberField_isArithFrobAt_iff P _).mp (IsArithFrobAt.arithFrobAt (𝓞 E) Gal(K/E) P.asIdeal)

/-- Nonramification makes the actual residue-power lift unique. -/
theorem numberField_frobenius_unique (P : HeightOneSpectrum (𝓞 K))
    [Algebra.IsUnramifiedAt (𝓞 E) P.asIdeal]
    (σ γ : Gal(K/E))
    (hσ : ∀ z : 𝓞 K, RingOfIntegers.mapRingEquiv σ.toRingEquiv z -
      z ^ (P.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K))).absNorm ∈ P.asIdeal)
    (hγ : ∀ z : 𝓞 K, RingOfIntegers.mapRingEquiv γ.toRingEquiv z -
      z ^ (P.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K))).absNorm ∈ P.asIdeal) : σ = γ := by
  have hs := (numberField_isArithFrobAt_iff P σ).mpr hσ
  have hg := (numberField_isArithFrobAt_iff P γ).mpr hγ
  have heq := hs.eq_of_isUnramifiedAt hg P.asIdeal.primeCompl_le_nonZeroDivisors
  let : FaithfulSMul Gal(K/E) (𝓞 K) := IsGaloisGroup.faithful (𝓞 E)
  exact FaithfulSMul.eq_of_smul_eq_smul (fun z : 𝓞 K =>
    congrArg (fun f : 𝓞 K →ₐ[𝓞 E] 𝓞 K => f z) heq)

/-- The coherent lifts at two primes above the same base prime are conjugate. -/
theorem numberFieldFrobenius_isConj (P Q : HeightOneSpectrum (𝓞 K))
    (hPQ : P.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) =
      Q.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K))) :
    IsConj (numberFieldFrobenius (E := E) P) (numberFieldFrobenius (E := E) Q) :=
  isConj_arithFrobAt (𝓞 E) Gal(K/E) P.asIdeal Q.asIdeal hPQ

end
end SimultaneousPrimitiveRoots
