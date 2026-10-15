import SimultaneousPrimitiveRootsFinal.SUnitHilbertPreparation

/-!
# A common sufficient support for two exponents

Enlarge successively for both exponents. The enlargement operations commute,
so each injectivity/cardinality theorem applies on the same finite set.
This identifies the supports, not the Hilbert pairings at different exponents.
-/

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional.CFTBridge

open ClassFieldTheory Arithmetic NumberField IsDedekindDomain
open GlobalClassFieldTheory.GlobalClassFields
open scoped NumberField

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]

/-- The enlargement order does not matter: both add a fixed class support and exponent support. -/
theorem sUnitKummerNormSupport_comm
    (seed : Finset (HeightOneSpectrum (𝓞 F))) (m n : ℕ+) :
    sUnitKummerNormSupport (K := F) m (sUnitKummerNormSupport (K := F) n seed) =
      sUnitKummerNormSupport (K := F) n (sUnitKummerNormSupport (K := F) m seed) := by
  classical
  ext v
  simp only [sUnitKummerNormSupport, Finset.mem_union]
  tauto

/-- Both localization maps are injective on this single common support. -/
theorem sUnitPowerLocalization_injective_on_commonSupport
    (seed : Finset (HeightOneSpectrum (𝓞 F))) (m n : ℕ+)
    (hm : (primitiveRoots (m : ℕ) F).Nonempty)
    (hn : (primitiveRoots (n : ℕ) F).Nonempty) :
    let S := sUnitKummerNormSupport (K := F) m (sUnitKummerNormSupport (K := F) n seed)
    Function.Injective (sUnitPowerLocalization F S m) ∧
      Function.Injective (sUnitPowerLocalization F S n) := by
  dsimp only
  constructor
  · exact sUnitPowerLocalization_injective_on_kummerNormSupport F _ m hm
  · rw [sUnitKummerNormSupport_comm F seed m n]
    exact sUnitPowerLocalization_injective_on_kummerNormSupport F _ n hn

/-- The image-size formula holds for both exponents on the same local product. -/
theorem sUnitPowerLocalization_card_sq_on_commonSupport
    (seed : Finset (HeightOneSpectrum (𝓞 F))) (m n : ℕ+)
    (hm : (primitiveRoots (m : ℕ) F).Nonempty)
    (hn : (primitiveRoots (n : ℕ) F).Nonempty) :
    let S := sUnitKummerNormSupport (K := F) m (sUnitKummerNormSupport (K := F) n seed)
    (Nat.card (sUnitPowerLocalization F S m).range ^ 2 =
      Nat.card (∀ v : S, PowerClassGroup (v.1.adicCompletion F) m)) ∧
    (Nat.card (sUnitPowerLocalization F S n).range ^ 2 =
      Nat.card (∀ v : S, PowerClassGroup (v.1.adicCompletion F) n)) := by
  dsimp only
  constructor
  · exact sUnitPowerLocalization_card_sq_on_kummerNormSupport F _ m hm
  · rw [sUnitKummerNormSupport_comm F seed m n]
    exact sUnitPowerLocalization_card_sq_on_kummerNormSupport F _ n hn

/-- Both exponents are local units outside the common support. -/
theorem valuation_exponents_eq_one_outside_commonSupport
    (seed : Finset (HeightOneSpectrum (𝓞 F))) (m n : ℕ+)
    {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ sUnitKummerNormSupport (K := F) m (sUnitKummerNormSupport (K := F) n seed)) :
    v.valuation F ((m : ℕ) : F) = 1 ∧ v.valuation F ((n : ℕ) : F) = 1 := by
  constructor
  · exact valuation_natCast_eq_one_of_not_mem_sUnitKummerNormSupport m _ hv
  · rw [sUnitKummerNormSupport_comm F seed m n] at hv
    exact valuation_natCast_eq_one_of_not_mem_sUnitKummerNormSupport n _ hv

end SimultaneousPrimitiveRoots.Unconditional.CFTBridge
