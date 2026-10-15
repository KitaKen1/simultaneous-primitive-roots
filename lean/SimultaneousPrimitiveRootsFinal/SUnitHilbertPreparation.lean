import SimultaneousPrimitiveRootsFinal.SUnitHilbertComplement
import SimultaneousPrimitiveRootsFinal.SUnitPowerClasses
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SUnitKummerNormCore

/-!
# Finite S-unit Hilbert preparation on an actual sufficient support

Reuse CFT's Kummer norm support and principal-kernel theorem. This proves
localization injectivity and the squared-cardinality formula for that
support, discharging the cardinality input of the coherent complement.
Supports for different exponents are not identified here, and no compact
balanced representatives or analytic evaluation is asserted.
-/

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional.CFTBridge

open ClassFieldTheory Arithmetic NumberField IsDedekindDomain
open GlobalClassFieldTheory.ClassFieldAxiom
open GlobalClassFieldTheory.GlobalClassFields
open scoped NumberField BigOperators

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]

omit [NumberField F] in
/-- Every positive power map is surjective at an infinite place of a totally complex field. -/
theorem infinitePlace_powerSubgroup_eq_top (n : ℕ+) (w : InfinitePlace F) :
    (powMonoidHom (n : ℕ) : w.Completionˣ →* w.Completionˣ).range = ⊤ := by
  have hw : ¬w.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr
    (IsTotallyComplex.isComplex w)
  rw [nthPowerSubgroup_eq_infinitePositiveSubgroup n w (Or.inr hw)]
  ext x
  simp [RayClass.mem_infinitePositiveSubgroup_iff, hw]

/-- CFT's principal-kernel equality gives injectivity of the actual localization map. -/
theorem sUnitPowerLocalization_injective_of_principalKernel
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ+)
    (hprincipal : principalIdelePowerLocalUnitSubgroup (K := F) n S ∅ =
      sUnitNthPowersInField (K := F) n S) :
    Function.Injective (sUnitPowerLocalization F S n) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro q hq
  obtain ⟨a, rfl⟩ := powerClassMk_surjective _ (n : ℕ) q
  have hloc := MonoidHom.mem_ker.mp hq
  have hprincipalA : (a : Fˣ) ∈ principalIdelePowerLocalUnitSubgroup (K := F) n S ∅ := by
    apply (mem_idelePowerLocalUnitSubgroup_iff n S ∅ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro w
      rw [infinitePlace_powerSubgroup_eq_top F n w]
      exact Subgroup.mem_top _
    · intro v hv
      have h := congrFun hloc ⟨v, hv⟩
      have hp : IdeleGroup.finiteComponent v (IdeleGroup.principalIdele F (a : Fˣ)) =
          Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom (a : Fˣ) := by
        apply Units.ext
        simp only [IdeleGroup.finiteComponent_principalIdele, Units.coe_map]
        rfl
      rw [hp]
      exact (QuotientGroup.eq_one_iff _).mp h
    · intro v hv
      have hvS : v ∉ S := by simpa only [Finset.union_empty] using hv
      rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
      rw [IdeleGroup.finiteComponent_principalIdele,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact a.property v hvS
  rw [hprincipal] at hprincipalA
  obtain ⟨b, hb, hba⟩ := hprincipalA
  have hba' : b = a := Subtype.ext hba
  change powerClassMk _ (n : ℕ) a = 1
  exact (QuotientGroup.eq_one_iff a).mpr (hba' ▸ hb)

/-- The sufficient support is selected by the existing CFT construction. -/
theorem sUnitPowerLocalization_injective_on_kummerNormSupport
    (seed : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty) :
    Function.Injective (sUnitPowerLocalization F (sUnitKummerNormSupport (K := F) n seed) n) :=
  sUnitPowerLocalization_injective_of_principalKernel F _ n
    (principalIdelePowerLocalUnitSubgroup_eq_sUnitNthPowers_on_kummerNormSupport n hmu seed)

/-- In a totally complex field the supported-idele index is exactly the finite local index. -/
theorem localPowerClassProduct_card
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (hS : ∀ v : HeightOneSpectrum (𝓞 F),
      v.asIdeal ∣ Ideal.span {((n : ℕ) : 𝓞 F)} → v ∈ S) :
    Nat.card (∀ v : S, PowerClassGroup (v.1.adicCompletion F) n) =
      (n : ℕ) ^ (2 * (Fintype.card (InfinitePlace F) + S.card)) := by
  have hInf : Nat.card (∀ w : InfinitePlace F,
      w.Completionˣ ⧸ (powMonoidHom (n : ℕ) : w.Completionˣ →* w.Completionˣ).range) = 1 := by
    rw [Nat.card_pi]
    apply Finset.prod_eq_one
    intro w _
    have hw : ¬w.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr
      (IsTotallyComplex.isComplex w)
    simp only [card_infinitePlace_nthPowerQuotient, hw, false_and, ite_false]
  have h := card_supportedIdeleQuotient_eq_power_two_totalPlaceCard (K := F) n hmu S ∅ hS
  rw [card_supportedIdeleQuotient_eq_localPowerClasses, Nat.card_prod, hInf, one_mul] at h
  exact h

/-- The actual image has half the exponent of the local product's cardinality. -/
theorem sUnitPowerLocalization_card_sq_on_kummerNormSupport
    (seed : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty) :
    let S := sUnitKummerNormSupport (K := F) n seed
    Nat.card (sUnitPowerLocalization F S n).range ^ 2 =
      Nat.card (∀ v : S, PowerClassGroup (v.1.adicCompletion F) n) := by
  dsimp only
  let S := sUnitKummerNormSupport (K := F) n seed
  have hcard := sUnitPowerClass_range_card F S n hmu (sUnitPowerLocalization F S n)
    (sUnitPowerLocalization_injective_on_kummerNormSupport F seed n hmu)
  rw [hcard, localPowerClassProduct_card F S n hmu
    (fun v hv => mem_sUnitKummerNormSupport_of_asIdeal_dvd_natCast n seed hv)]
  rw [← pow_mul, Nat.mul_comm]

/-- **CFT discharges both global isotropy and cardinality on the chosen support.** -/
theorem exists_sUnit_prime_hilbert_preparation
    (seed : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ+) [Fact (n : ℕ).Prime]
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (hmu2 : (primitiveRoots (2 * (n : ℕ)) F).Nonempty) :
    let S := sUnitKummerNormSupport (K := F) n seed
    ∃ B : GlobalHilbertPairingFamily F n,
      IsCoherentHilbertFamily F n hmu B ∧
      (∀ x ∈ (sUnitPowerLocalization F S n).range,
        ∀ y ∈ (sUnitPowerLocalization F S n).range,
          piPairing (fun v : S => finitePlaceGlobalRootPairing F n hmu B v) x y = 1) ∧
      (∀ x, (∀ y ∈ (sUnitPowerLocalization F S n).range,
        piPairing (fun v : S => finitePlaceGlobalRootPairing F n hmu B v) x y = 1) →
        x ∈ (sUnitPowerLocalization F S n).range) ∧
      ∃ C : Subgroup (∀ v : S, PowerClassGroup (v.1.adicCompletion F) n),
        IsCompl (sUnitPowerLocalization F S n).range C ∧
        ∀ x ∈ C, ∀ y ∈ C,
          piPairing (fun v : S => finitePlaceGlobalRootPairing F n hmu B v) x y = 1 := by
  dsimp only
  exact exists_sUnit_prime_hilbert_compl_of_card F _ n hmu hmu2
    (fun _ hv => valuation_natCast_eq_one_of_not_mem_sUnitKummerNormSupport n seed hv)
    (sUnitPowerLocalization_card_sq_on_kummerNormSupport F seed n hmu)

end SimultaneousPrimitiveRoots.Unconditional.CFTBridge
