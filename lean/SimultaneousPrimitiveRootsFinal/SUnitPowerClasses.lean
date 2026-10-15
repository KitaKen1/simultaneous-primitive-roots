import SimultaneousPrimitiveRoots.Unconditional.Arithmetic.PowerClasses
import ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.SUnitPowerQuotient

/-!
# Actual power classes of S-units

Reuse the CFT S-unit theorem instead of rebuilding the logarithmic lattice.
These results describe the source of the localization map. Injectivity into
the product of local power classes is a separate arithmetic statement.
-/

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional.CFTBridge

open Arithmetic NumberField IsDedekindDomain
open scoped NumberField

variable (F : Type*) [Field F] [NumberField F]

/-- The actual S-unit power quotient is finite at every positive exponent. -/
theorem sUnitPowerClass_finite (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ+) :
    Finite (PowerClass (SUnitGroup (K := F) S) (n : ℕ)) :=
  KummerTheory.finite_sUnit_nthPowerQuotient S n

/-- The roots-of-unity coordinate contributes the extra factor of `n`. -/
theorem sUnitPowerClass_card (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty) :
    Nat.card (PowerClass (SUnitGroup (K := F) S) (n : ℕ)) =
      (n : ℕ) ^ (Fintype.card (InfinitePlace F) + S.card) :=
  KummerTheory.card_sUnit_nthPowerQuotient S n hmu

/-- Coordinates supplied by the existing S-unit decomposition. -/
def sUnitPowerClassCoordinates (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty) :
    PowerClass (SUnitGroup (K := F) S) (n : ℕ) ≃*
      Multiplicative (ZMod (n : ℕ)) ×
        Multiplicative (Fin (SUnitGroup.logRank (K := F) S) → ZMod (n : ℕ)) :=
  KummerTheory.sUnitNthPowerQuotientCoordinates S n hmu

/-- An injective localization retains exactly the S-unit quotient cardinality. -/
theorem sUnitPowerClass_range_card (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    {V : Type*} [CommGroup V]
    (f : PowerClass (SUnitGroup (K := F) S) (n : ℕ) →* V)
    (hf : Function.Injective f) :
    Nat.card f.range = (n : ℕ) ^ (Fintype.card (InfinitePlace F) + S.card) := by
  rw [← sUnitPowerClass_card F S n hmu]
  exact Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm

end SimultaneousPrimitiveRoots.Unconditional.CFTBridge
