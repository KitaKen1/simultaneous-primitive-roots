import SimultaneousPrimitiveRootsFinal.Remaining
import SimultaneousPrimitiveRootsFinal.TypeII.MarkedTransferBridge
import SimultaneousPrimitiveRootsFinal.TypeII.LongCoefficientBridge

/-!
# The main theorem, with no hypothesis

`SimultaneousPrimitiveRoots.MainClaim` (`SimultaneousPrimitiveRoots/Statement.lean`) is Theorem 1.1
of the public paper *Positive Lower Density of Simultaneous Primitive Roots*: for every admissible
finite set `A` of integers `≥ 2` there are `c > 0` and `x₀` such that at least `c · x / log x`
primes `p ∈ (x, 2x]` have every `a ∈ A` as a primitive root, for all `x ≥ x₀`.

`Remaining.lean` proves it from the statements of three theorems of the vendored formalization of
[A] (`mainClaim_of_openInputs`); the two files `TypeII/MarkedTransferBridge.lean` and
`TypeII/LongCoefficientBridge.lean` import those theorems. This file puts them together.

Expected axioms of `mainClaim`: `propext`, `Classical.choice`, `Quot.sound`
(`verification/MainClaimAxioms.lean`).
-/

namespace SimultaneousPrimitiveRoots

open Unconditional in
/-- **Positive lower density of simultaneous primitive roots** (Theorem 1.1 of the public paper),
with no analytic hypothesis. -/
theorem mainClaim : MainClaim :=
  mainClaim_of_openInputs vendoredMarkedCoefficientTransfer vendoredRoughLowFrequency
    vendoredRoughHighFrequency

end SimultaneousPrimitiveRoots
