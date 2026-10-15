import ArtinPrimitiveRoots.TypeII.Rough
import SimultaneousPrimitiveRootsFinal.TypeII.LongCoefficientReduction

/-!
# [P] Lemma 5.2 (the long coefficient) is a theorem

`TypeII/LongCoefficientReduction.lean` proves `Supply.PrimeMinusRoughLongCoefficient`
([P] Lemma 5.2, `[P-05:0044–0055]`) from the propositions `VendoredRoughLowFrequency` and
`VendoredRoughHighFrequency`, which are the statements of the vendored theorems
`ArtinPrimitiveRoots.TypeII.Rough.low_frequency` and
`ArtinPrimitiveRoots.TypeII.Rough.high_frequency` (`vendor/ArtinPrimitiveRoots/TypeII/Rough.lean`)
with `vendoredRoughCoefficient`, a copy of the definition of
`ArtinPrimitiveRoots.TypeII.Rough.roughCoefficient`. This file imports the two theorems and
discharges the hypotheses. It is kept separate because the import closure of
`ArtinPrimitiveRoots.TypeII.Rough` is large.
-/

namespace SimultaneousPrimitiveRoots.Unconditional

/-- The copy of the vendored coefficient is the vendored coefficient. -/
theorem vendoredRoughCoefficient_eq (x γ v : ℝ) (m : ℕ) :
    vendoredRoughCoefficient x γ v m =
      ArtinPrimitiveRoots.TypeII.Rough.roughCoefficient x γ v m := rfl

/-- The vendored low-frequency theorem is the first hypothesis of the reduction. -/
theorem vendoredRoughLowFrequency : VendoredRoughLowFrequency :=
  ArtinPrimitiveRoots.TypeII.Rough.low_frequency

/-- The vendored high-frequency theorem is the second hypothesis of the reduction. -/
theorem vendoredRoughHighFrequency : VendoredRoughHighFrequency :=
  ArtinPrimitiveRoots.TypeII.Rough.high_frequency

/-- **[P] Lemma 5.2** `maj:long-coefficient` (`[P-05:0044–0055]`) is a theorem: the supply-side
hypothesis `Supply.PrimeMinusRoughLongCoefficient` holds. -/
theorem Supply.primeMinusRoughLongCoefficient : Supply.PrimeMinusRoughLongCoefficient :=
  primeMinusRoughLongCoefficient_of_vendored vendoredRoughLowFrequency vendoredRoughHighFrequency

end SimultaneousPrimitiveRoots.Unconditional
