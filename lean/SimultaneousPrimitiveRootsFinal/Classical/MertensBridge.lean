import OAI.NumberTheory.JointDickman.Arithmetic.MertensDischarge
import SimultaneousPrimitiveRoots.Unconditional.Supply.ClassicalInputs

/-!
# The two Mertens estimates ([P] Lemma 2.1) from the vendored OpenAI library

`Supply.MertensReciprocal` and `Supply.MertensProduct` (`Supply/ClassicalInputs.lean`) are the
statements `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput` and
`PrimeProductMertensInput`, which `vendor/OAI/NumberTheory/JointDickman/Arithmetic/MertensDischarge.lean`
proves from the vendored `PrimeNumberTheoremAnd.Erdos970.MertensClassical`.
-/

namespace SimultaneousPrimitiveRoots.Unconditional

/-- **Mertens' estimate for `∑ 1/p`** ([P] Lemma 2.1) is a theorem: the supply-side hypothesis
`Supply.MertensReciprocal` holds. -/
theorem Supply.mertensReciprocalEstimate : Supply.MertensReciprocal :=
  OAI.JointDickman.primeReciprocalMertensInput

/-- **Mertens' product theorem** ([P] Lemma 2.1) is a theorem: the supply-side hypothesis
`Supply.MertensProduct` holds. -/
theorem Supply.mertensProductEstimate : Supply.MertensProduct :=
  OAI.JointDickman.primeProductMertensInput

end SimultaneousPrimitiveRoots.Unconditional
