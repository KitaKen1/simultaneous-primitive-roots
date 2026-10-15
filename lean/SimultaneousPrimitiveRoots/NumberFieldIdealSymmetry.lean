module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section

/-- Forward ideal images commute with contraction in a commuting
square of actual ring automorphisms. -/
theorem idealMap_comap_commuting {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (ρ : R ≃+* R) (τ : S ≃+* S)
    (hcomm : ∀ x, τ (f x) = f (ρ x)) (I : Ideal S) :
    (I.map τ).comap f = (I.comap f).map ρ := by
  rw [← Ideal.comap_symm τ, ← Ideal.comap_symm ρ]
  ext x
  simp only [Ideal.mem_comap]
  have hx : τ.symm (f x) = f (ρ.symm x) := by
    apply τ.injective
    rw [τ.apply_symm_apply, hcomm, ρ.apply_symm_apply]
  rw [hx]

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]

/-- Absolute ideal norms are preserved because the actual quotient rings
are isomorphic. No basis, ramification-index or analytic input is used. -/
theorem numberFieldIdeal_map_absNorm (e : K ≃+* L) (I : Ideal (𝓞 K)) :
    (I.map (RingOfIntegers.mapRingEquiv e)).absNorm = I.absNorm := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr
    (Ideal.quotientEquiv I (I.map (RingOfIntegers.mapRingEquiv e))
      (RingOfIntegers.mapRingEquiv e) rfl).symm.toEquiv

/-- The actual nonzero prime ideals, with the forward image orientation. -/
def numberFieldPrimeIdealEquiv (e : K ≃+* L) :
    HeightOneSpectrum (𝓞 K) ≃ HeightOneSpectrum (𝓞 L) :=
  HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)

omit [NumberField K] [NumberField L] in
theorem numberFieldPrimeIdealEquiv_asIdeal (e : K ≃+* L)
    (P : HeightOneSpectrum (𝓞 K)) :
    (numberFieldPrimeIdealEquiv e P).asIdeal =
      P.asIdeal.map (RingOfIntegers.mapRingEquiv e) := by
  exact Ideal.comap_symm (RingOfIntegers.mapRingEquiv e)

theorem numberFieldPrimeIdealEquiv_absNorm (e : K ≃+* L)
    (P : HeightOneSpectrum (𝓞 K)) :
    (numberFieldPrimeIdealEquiv e P).asIdeal.absNorm = P.asIdeal.absNorm := by
  rw [numberFieldPrimeIdealEquiv_asIdeal, numberFieldIdeal_map_absNorm]

omit [NumberField K] [NumberField L] in
theorem numberFieldPrimeIdealEquiv_natCast_mem (e : K ≃+* L)
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (n : 𝓞 L) ∈ (numberFieldPrimeIdealEquiv e P).asIdeal ↔ (n : 𝓞 K) ∈ P.asIdeal := by
  rw [numberFieldPrimeIdealEquiv_asIdeal,
    ← map_natCast (RingOfIntegers.mapRingEquiv e), Ideal.apply_mem_of_equiv_iff]

/-- Prime-ideal powers retain their norm as well, including ramified primes. -/
theorem numberFieldPrimeIdealEquiv_power_absNorm (e : K ≃+* L)
    (P : HeightOneSpectrum (𝓞 K)) (j : ℕ) :
    ((numberFieldPrimeIdealEquiv e P).asIdeal ^ j).absNorm = (P.asIdeal ^ j).absNorm := by
  rw [map_pow, map_pow, numberFieldPrimeIdealEquiv_absNorm]

end
end SimultaneousPrimitiveRoots
