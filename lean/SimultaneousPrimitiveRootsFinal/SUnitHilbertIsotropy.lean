import SimultaneousPrimitiveRootsFinal.HilbertUnitSymbols
import SimultaneousPrimitiveRootsFinal.LocalHilbertProducts
import ClassFieldTheory.Theorems.HilbertSymbols.HilbertProductFormula
import ClassFieldTheory.AlgebraicNumberTheory.Idele.SPlaces
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# The actual S-unit image is isotropic

Use the coherent family from the global Hilbert product formula. Away from
S, the two S-units and the exponent are valuation-ring units, so the local
factor is one. In a totally complex field every infinite factor is one.
This proves isotropy of the joint image; it does not prove its injectivity,
the squared-cardinality formula, or compatibility between exponents.
-/

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional.CFTBridge

open ClassFieldTheory Arithmetic NumberField IsDedekindDomain
open scoped NumberField BigOperators

variable (F : Type) [Field F] [NumberField F]

/-- Retain the global formula and finite support of the very same local family. -/
def IsCoherentHilbertFamily (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (B : GlobalHilbertPairingFamily F n) : Prop :=
  GlobalHilbertPairingFamily.IsLocallyHilbert F B ∧
    GlobalHilbertPairingFamily.HasFiniteSupport F B hmu ∧
    ∀ a b : Fˣ,
      (∏ v : InfinitePlace F, globalInfinitePlaceHilbertSymbol F n v a b) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 F),
          GlobalHilbertPairingFamily.finiteFactor F B hmu v a b = 1

/-- Valuation one is independent of the value-group model of a finite completion. -/
theorem finitePlaceCompletion_valuation_eq_one_iff
    (v : HeightOneSpectrum (𝓞 F)) (a : F) :
    letI : ValuativeRel (v.adicCompletion F) := finitePlaceCompletionValuativeRel F v
    ValuativeRel.valuation (v.adicCompletion F) (algebraMap F (v.adicCompletion F) a) = 1 ↔
      v.valuation F a = 1 := by
  let ν : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  let : ValuativeRel (v.adicCompletion F) := finitePlaceCompletionValuativeRel F v
  let : ν.Compatible := Valuation.Compatible.ofValuation ν
  have h : ValuativeRel.valuation (v.adicCompletion F)
      (algebraMap F (v.adicCompletion F) a) = 1 ↔
      ν (algebraMap F (v.adicCompletion F) a) = 1 := by
    simpa only [map_one] using
      ((ValuativeRel.valuation (v.adicCompletion F)).veq_iff_eq
        (x := algebraMap F (v.adicCompletion F) a) (y := 1)).symm.trans
          (ν.veq_iff_eq (x := algebraMap F (v.adicCompletion F) a) (y := 1))
  have hv : ν (algebraMap F (v.adicCompletion F) a) = v.valuation F a :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := F) (v := v) a
  exact h.trans (by rw [hv])

/-- A coherent local factor is one whenever its three global valuations are one. -/
theorem hilbertFiniteFactor_eq_one_of_valuation_eq_one
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (B : GlobalHilbertPairingFamily F n)
    (hB : GlobalHilbertPairingFamily.IsLocallyHilbert F B)
    (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ)
    (hn : v.valuation F ((n : ℕ) : F) = 1)
    (ha : v.valuation F (a : F) = 1) (hb : v.valuation F (b : F) = 1) :
    GlobalHilbertPairingFamily.finiteFactor F B hmu v a b = 1 := by
  let K := v.adicCompletion F
  let : ValuativeRel K := finitePlaceCompletionValuativeRel F v
  let : IsNonarchimedeanLocalField K := finitePlaceCompletionIsNonarchimedeanLocalField F v
  have hmuK : (primitiveRoots (n : ℕ) K).Nonempty := by
    obtain ⟨ζ, hζ⟩ := hmu
    exact ⟨algebraMap F K ζ, (mem_primitiveRoots n.pos).mpr
      (((mem_primitiveRoots n.pos).mp hζ).map_of_injective (algebraMap F K).injective)⟩
  have hlocal := hilbertPairing_symbol_eq_one_of_valuation_eq_one K n
    (by simpa only [map_natCast] using (finitePlaceCompletion_valuation_eq_one_iff F v _).mpr hn)
    hmuK (B v) (hB v).2.2.2
    (Units.map (algebraMap F K).toMonoidHom a)
    (Units.map (algebraMap F K).toMonoidHom b)
    ((finitePlaceCompletion_valuation_eq_one_iff F v _).mpr ha)
    ((finitePlaceCompletion_valuation_eq_one_iff F v _).mpr hb)
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let e : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) K :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap F K).injective hmu
  change e.symm ((B v).symbol
    (Units.map (algebraMap F K).toMonoidHom a)
    (Units.map (algebraMap F K).toMonoidHom b)) = 1
  rw [hlocal, map_one]

/-- Totally complex fields contribute no infinite Hilbert factors. -/
theorem hilbertInfiniteFactor_eq_one [IsTotallyComplex F]
    (n : ℕ+) (v : InfinitePlace F) (a b : Fˣ) :
    globalInfinitePlaceHilbertSymbol F n v a b = 1 := by
  have hv : ¬v.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr
    (IsTotallyComplex.isComplex v)
  simp [globalInfinitePlaceHilbertSymbol, hv]

/-- Restrict the actual global product formula to the finite S-unit places. -/
theorem sUnit_hilbertFiniteFactor_prod_eq_one [IsTotallyComplex F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (hS : ∀ v ∉ S, v.valuation F ((n : ℕ) : F) = 1)
    (B : GlobalHilbertPairingFamily F n)
    (hB : GlobalHilbertPairingFamily.IsLocallyHilbert F B)
    (hformula : ∀ a b : Fˣ,
      (∏ v : InfinitePlace F, globalInfinitePlaceHilbertSymbol F n v a b) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 F),
          GlobalHilbertPairingFamily.finiteFactor F B hmu v a b = 1)
    (a b : SUnitGroup (K := F) S) :
    ∏ v ∈ S, GlobalHilbertPairingFamily.finiteFactor F B hmu v a b = 1 := by
  classical
  have hs : Function.mulSupport (fun v =>
      GlobalHilbertPairingFamily.finiteFactor F B hmu v a b) ⊆ S := by
    intro v hv
    by_contra hvS
    exact hv (hilbertFiniteFactor_eq_one_of_valuation_eq_one F n hmu B hB v a b
      (hS v hvS) (a.property v hvS) (b.property v hvS))
  have h := hformula a b
  simp only [hilbertInfiniteFactor_eq_one, Finset.prod_const_one, one_mul] at h
  rwa [finprod_eq_prod_of_mulSupport_subset _ hs] at h

/-- The same global S-unit is used in every local power-class coordinate. -/
def sUnitPowerLocalization (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ+) :
    PowerClass (SUnitGroup (K := F) S) (n : ℕ) →*
      ∀ v : S, PowerClassGroup (v.1.adicCompletion F) n :=
  MonoidHom.pi fun v => powerClassMap
    ((Units.map (algebraMap F (v.1.adicCompletion F)).toMonoidHom).comp
      (SUnitGroup (K := F) S).subtype) (n : ℕ)

/-- Normalize a given local pairing to roots of unity in the global field. -/
def finitePlaceGlobalRootPairing (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (B : GlobalHilbertPairingFamily F n) (v : HeightOneSpectrum (𝓞 F)) :
    PowerClassGroup (v.adicCompletion F) n →*
      PowerClassGroup (v.adicCompletion F) n →* rootsOfUnity (n : ℕ) F := by
  letI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  exact commonRootPairing
    (rootsOfUnityEquivOfPrimitiveRoots (algebraMap F (v.adicCompletion F)).injective hmu).symm
    (B v)

/-- On representatives, the product pairing is exactly the restricted global formula. -/
theorem sUnitPowerLocalization_pairing_mk
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (B : GlobalHilbertPairingFamily F n) (a b : SUnitGroup (K := F) S) :
    piPairing (fun v : S => finitePlaceGlobalRootPairing F n hmu B v)
      (sUnitPowerLocalization F S n (powerClassMk _ (n : ℕ) a))
      (sUnitPowerLocalization F S n (powerClassMk _ (n : ℕ) b)) =
      ∏ v ∈ S, GlobalHilbertPairingFamily.finiteFactor F B hmu v a b := by
  change (∏ v : S, GlobalHilbertPairingFamily.finiteFactor F B hmu v a b) = _
  exact Finset.prod_coe_sort S
    (fun v : HeightOneSpectrum (𝓞 F) => GlobalHilbertPairingFamily.finiteFactor F B hmu v a b)

/-- The actual joint localization image of S-unit power classes is isotropic. -/
theorem sUnitPowerLocalization_isotropic [IsTotallyComplex F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (hS : ∀ v ∉ S, v.valuation F ((n : ℕ) : F) = 1)
    (B : GlobalHilbertPairingFamily F n)
    (hB : GlobalHilbertPairingFamily.IsLocallyHilbert F B)
    (hformula : ∀ a b : Fˣ,
      (∏ v : InfinitePlace F, globalInfinitePlaceHilbertSymbol F n v a b) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 F),
          GlobalHilbertPairingFamily.finiteFactor F B hmu v a b = 1) :
    ∀ x ∈ (sUnitPowerLocalization F S n).range,
      ∀ y ∈ (sUnitPowerLocalization F S n).range,
        piPairing (fun v : S => finitePlaceGlobalRootPairing F n hmu B v) x y = 1 := by
  rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
  obtain ⟨a, rfl⟩ := powerClassMk_surjective _ (n : ℕ) a
  obtain ⟨b, rfl⟩ := powerClassMk_surjective _ (n : ℕ) b
  rw [sUnitPowerLocalization_pairing_mk]
  exact sUnit_hilbertFiniteFactor_prod_eq_one F S n hmu hS B hB hformula a b

/-- CFT supplies a coherent family whose actual S-unit image is isotropic. -/
theorem exists_sUnit_hilbert_isotropic [IsTotallyComplex F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (hS : ∀ v ∉ S, v.valuation F ((n : ℕ) : F) = 1) :
    ∃ B : GlobalHilbertPairingFamily F n,
      IsCoherentHilbertFamily F n hmu B ∧
        ∀ x ∈ (sUnitPowerLocalization F S n).range,
          ∀ y ∈ (sUnitPowerLocalization F S n).range,
            piPairing (fun v : S => finitePlaceGlobalRootPairing F n hmu B v) x y = 1 := by
  obtain ⟨B, hB, hsupp, hformula⟩ := exists_globalHilbertPairingFamily_productFormula F n hmu
  exact ⟨B, ⟨hB, hsupp, hformula⟩,
    sUnitPowerLocalization_isotropic F S n hmu hS B hB hformula⟩

end SimultaneousPrimitiveRoots.Unconditional.CFTBridge
