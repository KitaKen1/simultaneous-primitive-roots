import ArtinPrimitiveRoots.TypeII.MarkedTransfer
import SimultaneousPrimitiveRootsFinal.TypeII.MarkedTransferReduction

/-!
# The marked Type II estimate in coefficient form is a theorem

`TypeII/MarkedTransferReduction.lean` proves `Supply.MarkedTypeIICoefficientForm`
([A] `lem:marked-coefficient-transfer`, [P] Theorem 3.1 in coefficient form) from the proposition
`VendoredMarkedCoefficientTransfer`, which is the statement of the vendored theorem
`ArtinPrimitiveRoots.TypeII.marked_coefficient_transfer`
(`vendor/ArtinPrimitiveRoots/TypeII/MarkedTransfer.lean`). This file imports that theorem and
discharges the hypothesis. It is kept separate because the import closure of
`ArtinPrimitiveRoots.TypeII.MarkedTransfer` is large (the PoissonDirichlet chain).
-/

namespace SimultaneousPrimitiveRoots.Unconditional

/-- The vendored theorem is the hypothesis of the reduction. -/
theorem vendoredMarkedCoefficientTransfer : VendoredMarkedCoefficientTransfer :=
  ArtinPrimitiveRoots.TypeII.marked_coefficient_transfer

/-- **The marked Type II estimate in coefficient form** ([A] `lem:marked-coefficient-transfer`,
`[A-08:0099–0251]`; [P] Theorem 3.1 for general coefficients) is a theorem: the supply-side
hypothesis `Supply.MarkedTypeIICoefficientForm` holds. -/
theorem Supply.markedTypeIICoefficientForm : Supply.MarkedTypeIICoefficientForm :=
  markedTypeIICoefficientForm_of_vendored vendoredMarkedCoefficientTransfer

end SimultaneousPrimitiveRoots.Unconditional
