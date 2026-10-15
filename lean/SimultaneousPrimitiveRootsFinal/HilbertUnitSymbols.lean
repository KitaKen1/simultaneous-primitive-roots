import ClassFieldTheory.LocalClassFieldTheory.Kummer.MathlibHilbertPairing
import ClassFieldTheory.LocalClassFieldTheory.Kummer.PowerResidueTameFormula

/-!
# Tame unit symbols for any local Hilbert pairing

The norm-residue criterion determines which values are one, even when the
value normalization is not fixed. This lets a coherent global family use
the existing tame unit theorem without comparing its nontrivial values.
-/

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional.CFTBridge

open ClassFieldTheory LocalFieldTheory IsNonarchimedeanLocalField
open scoped ValuativeRel

/-- Two norm-residue pairings have the same trivial symbols. -/
theorem hilbertPairing_symbol_eq_one_iff
    {K : Type*} [Field K] {n : ℕ+} (B C : HilbertPairing K n)
    (hB : B.SatisfiesNormResidueCriterion) (hC : C.SatisfiesNormResidueCriterion)
    (a b : Kˣ) : B.symbol a b = 1 ↔ C.symbol a b = 1 :=
  (hB a b).trans (hC a b).symm

/-- Tame integral units have trivial symbol for any local Hilbert pairing. -/
theorem hilbertPairing_integerUnit_symbol_eq_one
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ+)
    (hn : ValuativeRel.valuation K ((n : ℕ) : K) = 1)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (B : HilbertPairing K n) (hB : B.SatisfiesNormResidueCriterion)
    (u v : 𝒪[K]ˣ) :
    B.symbol (integerUnitsToFieldUnits K u) (integerUnitsToFieldUnits K v) = 1 := by
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    intro hz
    have h := hn
    rw [hz, map_zero] at h
    exact zero_ne_one h
  apply (hilbertPairing_symbol_eq_one_iff B (localHilbertPairing K n hnK hmu)
    hB (localHilbertPairing_isLocalHilbertPairing K n hnK hmu).2.2.2 _ _).mpr
  change localHilbertPairing K n hnK hmu
    (powerClass K n (integerUnitsToFieldUnits K u))
    (powerClass K n (integerUnitsToFieldUnits K v)) = 1
  rw [localHilbertPairing_powerClass]
  unfold ClassFieldTheory.localHilbertSymbol
  rw [LocalClassFieldTheory.Kummer.localHilbertSymbol_integerUnit_integerUnit_eq_one
    K n hn hmu u v, map_one]

/-- A field unit with valuation one comes from an integral unit. -/
theorem exists_integerUnit_of_valuation_eq_one
    (K : Type*) [Field K] [ValuativeRel K] (a : Kˣ)
    (ha : ValuativeRel.valuation K (a : K) = 1) :
    ∃ u : 𝒪[K]ˣ, integerUnitsToFieldUnits K u = a := by
  let aO : 𝒪[K] := ⟨(a : K), ha.le⟩
  have hu : IsUnit aO :=
    (Valuation.integer.integers (ValuativeRel.valuation K)).isUnit_iff_valuation_eq_one.mpr ha
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, ?_⟩
  apply Units.ext
  change ((u : 𝒪[K]) : K) = (a : K)
  rw [hu]

/-- Triviality depends only on the three valuation-one conditions. -/
theorem hilbertPairing_symbol_eq_one_of_valuation_eq_one
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ+)
    (hn : ValuativeRel.valuation K ((n : ℕ) : K) = 1)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (B : HilbertPairing K n) (hB : B.SatisfiesNormResidueCriterion)
    (a b : Kˣ) (ha : ValuativeRel.valuation K (a : K) = 1)
    (hb : ValuativeRel.valuation K (b : K) = 1) : B.symbol a b = 1 := by
  obtain ⟨u, rfl⟩ := exists_integerUnit_of_valuation_eq_one K a ha
  obtain ⟨v, rfl⟩ := exists_integerUnit_of_valuation_eq_one K b hb
  exact hilbertPairing_integerUnit_symbol_eq_one K n hn hmu B hB u v

end SimultaneousPrimitiveRoots.Unconditional.CFTBridge
